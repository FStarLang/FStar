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
  
let tc_subeff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let env0 = env  in
        let uu____253 = FStar_Syntax_Subst.open_sub_eff sub1  in
        match uu____253 with
        | (uvs,bs,sub2) ->
            let uu____261 = FStar_TypeChecker_TcTerm.tc_tparams env0 bs  in
            (match uu____261 with
             | (effect_binders,env1,uu____267) ->
                 ((let uu____269 =
                     FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                       (FStar_Options.Other "Lift")
                      in
                   if uu____269
                   then
                     let uu____270 =
                       FStar_Syntax_Print.sigelt_to_string
                         (FStar_Syntax_Syntax.Sig_sub_effect (sub2, r))
                        in
                     FStar_Util.print1 "After opening a sub effect %s\n"
                       uu____270
                   else ());
                  (let effect_wp_typ effect_lid effect_args =
                     let eff_signature =
                       FStar_TypeChecker_Env.lookup_effect_lid env1
                         effect_lid
                        in
                     let uu____280 =
                       monad_signature env1 effect_lid eff_signature  in
                     match uu____280 with
                     | (effect_bs,wp_typ) ->
                         let effect_args_sub =
                           FStar_List.map2
                             (fun uu____308  ->
                                fun uu____309  ->
                                  match (uu____308, uu____309) with
                                  | ((x,uu____323),(arg,uu____325)) ->
                                      FStar_Syntax_Syntax.NT (x, arg))
                             effect_bs effect_args
                            in
                         let wp_typ1 =
                           FStar_Syntax_Subst.subst effect_args_sub wp_typ
                            in
                         let uu____339 =
                           let uu____340 = FStar_Syntax_Util.type_u ()  in
                           FStar_All.pipe_left Prims.fst uu____340  in
                         tc_check_trivial_guard env1 wp_typ1 uu____339
                      in
                   let source =
                     (sub2.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.comp_typ_name
                      in
                   let target =
                     (sub2.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.comp_typ_name
                      in
                   let src_wp =
                     effect_wp_typ source
                       (sub2.FStar_Syntax_Syntax.sub_eff_source).FStar_Syntax_Syntax.effect_args
                      in
                   let tgt_wp =
                     effect_wp_typ target
                       (sub2.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.effect_args
                      in
                   let tc_partial_comp_typ env2 ct wp_typ =
                     let bwp = FStar_Syntax_Syntax.new_bv None wp_typ  in
                     let env3 =
                       let uu____361 =
                         let uu____362 = FStar_Syntax_Syntax.mk_binder bwp
                            in
                         [uu____362]  in
                       FStar_TypeChecker_Env.push_binders env2 uu____361  in
                     let wp = FStar_Syntax_Syntax.bv_to_name bwp  in
                     let complete_effect =
                       let uu____367 =
                         let uu____370 =
                           let uu____371 =
                             let uu___86_372 = ct  in
                             let uu____373 =
                               let uu____379 =
                                 let uu____385 =
                                   FStar_Syntax_Syntax.as_arg wp  in
                                 [uu____385]  in
                               FStar_List.append
                                 ct.FStar_Syntax_Syntax.effect_args uu____379
                                in
                             {
                               FStar_Syntax_Syntax.comp_typ_name =
                                 (uu___86_372.FStar_Syntax_Syntax.comp_typ_name);
                               FStar_Syntax_Syntax.comp_univs =
                                 (uu___86_372.FStar_Syntax_Syntax.comp_univs);
                               FStar_Syntax_Syntax.effect_args = uu____373;
                               FStar_Syntax_Syntax.flags =
                                 (uu___86_372.FStar_Syntax_Syntax.flags)
                             }  in
                           FStar_Syntax_Syntax.Comp uu____371  in
                         FStar_Syntax_Syntax.mk uu____370  in
                       uu____367 None FStar_Range.dummyRange  in
                     let uu____398 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 complete_effect
                        in
                     match uu____398 with
                     | (c,uu____403,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                          (match c.FStar_Syntax_Syntax.n with
                           | FStar_Syntax_Syntax.Comp ct1 ->
                               ct1.FStar_Syntax_Syntax.comp_univs
                           | uu____407 ->
                               failwith
                                 "Impossible : typechecking a Comp should result in a Comp"))
                      in
                   let src_univs =
                     tc_partial_comp_typ env1
                       sub2.FStar_Syntax_Syntax.sub_eff_source src_wp
                      in
                   let tgt_univs =
                     tc_partial_comp_typ env1
                       sub2.FStar_Syntax_Syntax.sub_eff_target tgt_wp
                      in
                   let uu____410 =
                     match ((sub2.FStar_Syntax_Syntax.sub_eff_lift),
                             (sub2.FStar_Syntax_Syntax.sub_eff_lift_wp))
                     with
                     | (None ,None ) ->
                         failwith
                           "Impossible : a subEffect without any lift should not be generated by desugaring"
                     | (lift,Some lift_wp) ->
                         let expected_k =
                           let uu____430 =
                             let uu____431 =
                               FStar_Syntax_Syntax.null_binder src_wp  in
                             [uu____431]  in
                           let uu____432 =
                             FStar_Syntax_Syntax.mk_Total tgt_wp  in
                           FStar_Syntax_Util.arrow uu____430 uu____432  in
                         let uu____433 =
                           tc_check_trivial_guard env1 lift_wp expected_k  in
                         (lift, uu____433)
                     | (Some lift,None ) ->
                         let dmff_env =
                           FStar_TypeChecker_DMFF.empty env1
                             (FStar_TypeChecker_TcTerm.tc_constant
                                FStar_Range.dummyRange)
                            in
                         let uu____439 =
                           FStar_TypeChecker_DMFF.star_expr dmff_env lift  in
                         (match uu____439 with
                          | (uu____446,lift_wp,lift_elab) ->
                              let uu____449 =
                                recheck_debug "lift-wp" env1 lift_wp  in
                              let uu____450 =
                                recheck_debug "lift-elab" env1 lift_elab  in
                              ((Some lift_elab), lift_wp))
                      in
                   match uu____410 with
                   | (lift,lift_wp) ->
                       let env2 =
                         let uu___87_457 = env1  in
                         {
                           FStar_TypeChecker_Env.solver =
                             (uu___87_457.FStar_TypeChecker_Env.solver);
                           FStar_TypeChecker_Env.range =
                             (uu___87_457.FStar_TypeChecker_Env.range);
                           FStar_TypeChecker_Env.curmodule =
                             (uu___87_457.FStar_TypeChecker_Env.curmodule);
                           FStar_TypeChecker_Env.gamma =
                             (uu___87_457.FStar_TypeChecker_Env.gamma);
                           FStar_TypeChecker_Env.gamma_cache =
                             (uu___87_457.FStar_TypeChecker_Env.gamma_cache);
                           FStar_TypeChecker_Env.modules =
                             (uu___87_457.FStar_TypeChecker_Env.modules);
                           FStar_TypeChecker_Env.expected_typ =
                             (uu___87_457.FStar_TypeChecker_Env.expected_typ);
                           FStar_TypeChecker_Env.sigtab =
                             (uu___87_457.FStar_TypeChecker_Env.sigtab);
                           FStar_TypeChecker_Env.is_pattern =
                             (uu___87_457.FStar_TypeChecker_Env.is_pattern);
                           FStar_TypeChecker_Env.instantiate_imp =
                             (uu___87_457.FStar_TypeChecker_Env.instantiate_imp);
                           FStar_TypeChecker_Env.effects =
                             (uu___87_457.FStar_TypeChecker_Env.effects);
                           FStar_TypeChecker_Env.generalize =
                             (uu___87_457.FStar_TypeChecker_Env.generalize);
                           FStar_TypeChecker_Env.letrecs =
                             (uu___87_457.FStar_TypeChecker_Env.letrecs);
                           FStar_TypeChecker_Env.top_level =
                             (uu___87_457.FStar_TypeChecker_Env.top_level);
                           FStar_TypeChecker_Env.check_uvars =
                             (uu___87_457.FStar_TypeChecker_Env.check_uvars);
                           FStar_TypeChecker_Env.use_eq =
                             (uu___87_457.FStar_TypeChecker_Env.use_eq);
                           FStar_TypeChecker_Env.is_iface =
                             (uu___87_457.FStar_TypeChecker_Env.is_iface);
                           FStar_TypeChecker_Env.admit =
                             (uu___87_457.FStar_TypeChecker_Env.admit);
                           FStar_TypeChecker_Env.lax = true;
                           FStar_TypeChecker_Env.lax_universes =
                             (uu___87_457.FStar_TypeChecker_Env.lax_universes);
                           FStar_TypeChecker_Env.type_of =
                             (uu___87_457.FStar_TypeChecker_Env.type_of);
                           FStar_TypeChecker_Env.universe_of =
                             (uu___87_457.FStar_TypeChecker_Env.universe_of);
                           FStar_TypeChecker_Env.use_bv_sorts =
                             (uu___87_457.FStar_TypeChecker_Env.use_bv_sorts);
                           FStar_TypeChecker_Env.qname_and_index =
                             (uu___87_457.FStar_TypeChecker_Env.qname_and_index)
                         }  in
                       let repr_type eff_name effect_args wp =
                         let no_reify l =
                           let uu____478 =
                             let uu____479 =
                               let uu____482 =
                                 FStar_Util.format1
                                   "Effect %s cannot be reified"
                                   l.FStar_Ident.str
                                  in
                               let uu____483 =
                                 FStar_TypeChecker_Env.get_range env2  in
                               (uu____482, uu____483)  in
                             FStar_Errors.Error uu____479  in
                           Prims.raise uu____478  in
                         let uu____486 =
                           FStar_TypeChecker_Env.effect_decl_opt env2
                             eff_name
                            in
                         match uu____486 with
                         | None  -> no_reify eff_name
                         | Some ed ->
                             let univ_inst =
                               FStar_List.map
                                 (fun uu____493  ->
                                    FStar_Syntax_Syntax.U_unknown)
                                 ed.FStar_Syntax_Syntax.univs
                                in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with
                                 univ_inst env2 ed
                                 ([], (ed.FStar_Syntax_Syntax.repr))
                                in
                             let uu____496 =
                               let uu____497 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.qualifiers
                                   (FStar_List.contains
                                      FStar_Syntax_Syntax.Reifiable)
                                  in
                               Prims.op_Negation uu____497  in
                             if uu____496
                             then no_reify eff_name
                             else
                               (let uu____502 =
                                  FStar_TypeChecker_Env.get_range env2  in
                                let uu____503 =
                                  let uu____506 =
                                    let uu____507 =
                                      let uu____517 =
                                        let uu____519 =
                                          let uu____521 =
                                            FStar_Syntax_Syntax.as_arg wp  in
                                          [uu____521]  in
                                        FStar_List.append effect_args
                                          uu____519
                                         in
                                      (repr, uu____517)  in
                                    FStar_Syntax_Syntax.Tm_app uu____507  in
                                  FStar_Syntax_Syntax.mk uu____506  in
                                uu____503 None uu____502)
                          in
                       let tc_lift lift1 =
                         let wp_a = FStar_Syntax_Syntax.new_bv None src_wp
                            in
                         let wp_a_typ = FStar_Syntax_Syntax.bv_to_name wp_a
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
                               env2 lift_wp
                              in
                           let lift_wp_a =
                             let uu____547 =
                               FStar_TypeChecker_Env.get_range env2  in
                             let uu____548 =
                               let uu____551 =
                                 let uu____552 =
                                   let uu____562 =
                                     let uu____564 =
                                       FStar_Syntax_Syntax.as_arg wp_a_typ
                                        in
                                     [uu____564]  in
                                   (lift_wp1, uu____562)  in
                                 FStar_Syntax_Syntax.Tm_app uu____552  in
                               FStar_Syntax_Syntax.mk uu____551  in
                             uu____548 None uu____547  in
                           repr_type target
                             (sub2.FStar_Syntax_Syntax.sub_eff_target).FStar_Syntax_Syntax.effect_args
                             lift_wp_a
                            in
                         let expected_k =
                           let bs1 =
                             let uu____577 =
                               FStar_Syntax_Syntax.mk_binder wp_a  in
                             let uu____578 =
                               let uu____580 =
                                 FStar_Syntax_Syntax.null_binder repr_f  in
                               [uu____580]  in
                             uu____577 :: uu____578  in
                           let uu____581 =
                             FStar_Syntax_Syntax.mk_Total repr_result  in
                           FStar_Syntax_Util.arrow bs1 uu____581  in
                         let uu____582 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env2
                             expected_k
                            in
                         match uu____582 with
                         | (expected_k1,uu____587,uu____588) ->
                             tc_check_trivial_guard env2 lift1 expected_k1
                          in
                       let lift1 = FStar_Util.map_opt lift tc_lift  in
                       let env3 = env0  in
                       let univs1 =
                         let t =
                           let wp_a = FStar_Syntax_Syntax.new_bv None src_wp
                              in
                           let wp_a_typ = FStar_Syntax_Syntax.bv_to_name wp_a
                              in
                           let complete_effect ct wp =
                             let uu____606 =
                               let uu____609 =
                                 let uu____610 =
                                   let uu___88_611 = ct  in
                                   let uu____612 =
                                     let uu____618 =
                                       let uu____624 =
                                         FStar_Syntax_Syntax.as_arg wp  in
                                       [uu____624]  in
                                     FStar_List.append
                                       ct.FStar_Syntax_Syntax.effect_args
                                       uu____618
                                      in
                                   {
                                     FStar_Syntax_Syntax.comp_typ_name =
                                       (uu___88_611.FStar_Syntax_Syntax.comp_typ_name);
                                     FStar_Syntax_Syntax.comp_univs =
                                       (uu___88_611.FStar_Syntax_Syntax.comp_univs);
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____612;
                                     FStar_Syntax_Syntax.flags =
                                       (uu___88_611.FStar_Syntax_Syntax.flags)
                                   }  in
                                 FStar_Syntax_Syntax.Comp uu____610  in
                               FStar_Syntax_Syntax.mk uu____609  in
                             uu____606 None FStar_Range.dummyRange  in
                           let src_eff =
                             let uu____638 =
                               let uu____639 =
                                 FStar_Syntax_Syntax.null_binder
                                   FStar_TypeChecker_Common.t_unit
                                  in
                               [uu____639]  in
                             let uu____640 =
                               complete_effect
                                 sub2.FStar_Syntax_Syntax.sub_eff_source
                                 wp_a_typ
                                in
                             FStar_Syntax_Util.arrow uu____638 uu____640  in
                           let tgt_eff =
                             let lifted_wp =
                               let uu____647 =
                                 let uu____648 =
                                   let uu____649 =
                                     FStar_Syntax_Syntax.as_arg wp_a_typ  in
                                   [uu____649]  in
                                 FStar_Syntax_Syntax.mk_Tm_app lift_wp
                                   uu____648
                                  in
                               uu____647 None FStar_Range.dummyRange  in
                             complete_effect
                               sub2.FStar_Syntax_Syntax.sub_eff_target
                               lifted_wp
                              in
                           let uu____654 =
                             let uu____655 =
                               let uu____659 =
                                 FStar_Syntax_Syntax.mk_binder wp_a  in
                               let uu____660 =
                                 let uu____662 =
                                   FStar_Syntax_Syntax.null_binder src_eff
                                    in
                                 [uu____662]  in
                               uu____659 :: uu____660  in
                             FStar_List.append effect_binders uu____655  in
                           FStar_Syntax_Util.arrow uu____654 tgt_eff  in
                         let uu____665 =
                           FStar_TypeChecker_Util.generalize_universes env3 t
                            in
                         FStar_All.pipe_right uu____665 Prims.fst  in
                       let sub3 =
                         {
                           FStar_Syntax_Syntax.sub_eff_univs = univs1;
                           FStar_Syntax_Syntax.sub_eff_binders =
                             effect_binders;
                           FStar_Syntax_Syntax.sub_eff_source =
                             (let uu___89_669 =
                                sub2.FStar_Syntax_Syntax.sub_eff_source  in
                              {
                                FStar_Syntax_Syntax.comp_typ_name =
                                  (uu___89_669.FStar_Syntax_Syntax.comp_typ_name);
                                FStar_Syntax_Syntax.comp_univs = src_univs;
                                FStar_Syntax_Syntax.effect_args =
                                  (uu___89_669.FStar_Syntax_Syntax.effect_args);
                                FStar_Syntax_Syntax.flags =
                                  (uu___89_669.FStar_Syntax_Syntax.flags)
                              });
                           FStar_Syntax_Syntax.sub_eff_target =
                             (let uu___90_670 =
                                sub2.FStar_Syntax_Syntax.sub_eff_target  in
                              {
                                FStar_Syntax_Syntax.comp_typ_name =
                                  (uu___90_670.FStar_Syntax_Syntax.comp_typ_name);
                                FStar_Syntax_Syntax.comp_univs = tgt_univs;
                                FStar_Syntax_Syntax.effect_args =
                                  (uu___90_670.FStar_Syntax_Syntax.effect_args);
                                FStar_Syntax_Syntax.flags =
                                  (uu___90_670.FStar_Syntax_Syntax.flags)
                              });
                           FStar_Syntax_Syntax.sub_eff_lift_wp =
                             (Some lift_wp);
                           FStar_Syntax_Syntax.sub_eff_lift = lift1
                         }  in
                       FStar_Syntax_Subst.close_sub_eff sub3)))
  
let rec tc_eff_decl :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.eff_decl
  =
  fun env0  ->
    fun ed  ->
      let uu____733 =
        FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____733 with
      | (effect_params_un,signature_un,opening) ->
          let uu____740 =
            FStar_TypeChecker_TcTerm.tc_tparams env0 effect_params_un  in
          (match uu____740 with
           | (effect_params,env,uu____746) ->
               let uu____747 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env signature_un
                  in
               (match uu____747 with
                | (signature,uu____751) ->
                    let ed1 =
                      let uu___91_753 = ed  in
                      {
                        FStar_Syntax_Syntax.qualifiers =
                          (uu___91_753.FStar_Syntax_Syntax.qualifiers);
                        FStar_Syntax_Syntax.cattributes =
                          (uu___91_753.FStar_Syntax_Syntax.cattributes);
                        FStar_Syntax_Syntax.mname =
                          (uu___91_753.FStar_Syntax_Syntax.mname);
                        FStar_Syntax_Syntax.univs =
                          (uu___91_753.FStar_Syntax_Syntax.univs);
                        FStar_Syntax_Syntax.binders = effect_params;
                        FStar_Syntax_Syntax.signature = signature;
                        FStar_Syntax_Syntax.ret_wp =
                          (uu___91_753.FStar_Syntax_Syntax.ret_wp);
                        FStar_Syntax_Syntax.bind_wp =
                          (uu___91_753.FStar_Syntax_Syntax.bind_wp);
                        FStar_Syntax_Syntax.if_then_else =
                          (uu___91_753.FStar_Syntax_Syntax.if_then_else);
                        FStar_Syntax_Syntax.ite_wp =
                          (uu___91_753.FStar_Syntax_Syntax.ite_wp);
                        FStar_Syntax_Syntax.stronger =
                          (uu___91_753.FStar_Syntax_Syntax.stronger);
                        FStar_Syntax_Syntax.close_wp =
                          (uu___91_753.FStar_Syntax_Syntax.close_wp);
                        FStar_Syntax_Syntax.assert_p =
                          (uu___91_753.FStar_Syntax_Syntax.assert_p);
                        FStar_Syntax_Syntax.assume_p =
                          (uu___91_753.FStar_Syntax_Syntax.assume_p);
                        FStar_Syntax_Syntax.null_wp =
                          (uu___91_753.FStar_Syntax_Syntax.null_wp);
                        FStar_Syntax_Syntax.trivial =
                          (uu___91_753.FStar_Syntax_Syntax.trivial);
                        FStar_Syntax_Syntax.repr =
                          (uu___91_753.FStar_Syntax_Syntax.repr);
                        FStar_Syntax_Syntax.return_repr =
                          (uu___91_753.FStar_Syntax_Syntax.return_repr);
                        FStar_Syntax_Syntax.bind_repr =
                          (uu___91_753.FStar_Syntax_Syntax.bind_repr);
                        FStar_Syntax_Syntax.actions =
                          (uu___91_753.FStar_Syntax_Syntax.actions)
                      }  in
                    let ed2 =
                      match effect_params with
                      | [] -> ed1
                      | uu____757 ->
                          let op ts =
                            let t1 =
                              FStar_Syntax_Subst.subst opening (Prims.snd ts)
                               in
                            ([], t1)  in
                          let uu___92_775 = ed1  in
                          let uu____776 = op ed1.FStar_Syntax_Syntax.ret_wp
                             in
                          let uu____777 = op ed1.FStar_Syntax_Syntax.bind_wp
                             in
                          let uu____778 =
                            op ed1.FStar_Syntax_Syntax.if_then_else  in
                          let uu____779 = op ed1.FStar_Syntax_Syntax.ite_wp
                             in
                          let uu____780 = op ed1.FStar_Syntax_Syntax.stronger
                             in
                          let uu____781 = op ed1.FStar_Syntax_Syntax.close_wp
                             in
                          let uu____782 = op ed1.FStar_Syntax_Syntax.assert_p
                             in
                          let uu____783 = op ed1.FStar_Syntax_Syntax.assume_p
                             in
                          let uu____784 = op ed1.FStar_Syntax_Syntax.null_wp
                             in
                          let uu____785 = op ed1.FStar_Syntax_Syntax.trivial
                             in
                          let uu____786 =
                            let uu____787 =
                              op ([], (ed1.FStar_Syntax_Syntax.repr))  in
                            Prims.snd uu____787  in
                          let uu____793 =
                            op ed1.FStar_Syntax_Syntax.return_repr  in
                          let uu____794 =
                            op ed1.FStar_Syntax_Syntax.bind_repr  in
                          let uu____795 =
                            FStar_List.map
                              (fun a  ->
                                 let uu___93_798 = a  in
                                 let uu____799 =
                                   let uu____800 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_defn))
                                      in
                                   Prims.snd uu____800  in
                                 let uu____806 =
                                   let uu____807 =
                                     op
                                       ([],
                                         (a.FStar_Syntax_Syntax.action_typ))
                                      in
                                   Prims.snd uu____807  in
                                 {
                                   FStar_Syntax_Syntax.action_name =
                                     (uu___93_798.FStar_Syntax_Syntax.action_name);
                                   FStar_Syntax_Syntax.action_unqualified_name
                                     =
                                     (uu___93_798.FStar_Syntax_Syntax.action_unqualified_name);
                                   FStar_Syntax_Syntax.action_univs =
                                     (uu___93_798.FStar_Syntax_Syntax.action_univs);
                                   FStar_Syntax_Syntax.action_defn =
                                     uu____799;
                                   FStar_Syntax_Syntax.action_typ = uu____806
                                 }) ed1.FStar_Syntax_Syntax.actions
                             in
                          {
                            FStar_Syntax_Syntax.qualifiers =
                              (uu___92_775.FStar_Syntax_Syntax.qualifiers);
                            FStar_Syntax_Syntax.cattributes =
                              (uu___92_775.FStar_Syntax_Syntax.cattributes);
                            FStar_Syntax_Syntax.mname =
                              (uu___92_775.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.univs =
                              (uu___92_775.FStar_Syntax_Syntax.univs);
                            FStar_Syntax_Syntax.binders =
                              (uu___92_775.FStar_Syntax_Syntax.binders);
                            FStar_Syntax_Syntax.signature =
                              (uu___92_775.FStar_Syntax_Syntax.signature);
                            FStar_Syntax_Syntax.ret_wp = uu____776;
                            FStar_Syntax_Syntax.bind_wp = uu____777;
                            FStar_Syntax_Syntax.if_then_else = uu____778;
                            FStar_Syntax_Syntax.ite_wp = uu____779;
                            FStar_Syntax_Syntax.stronger = uu____780;
                            FStar_Syntax_Syntax.close_wp = uu____781;
                            FStar_Syntax_Syntax.assert_p = uu____782;
                            FStar_Syntax_Syntax.assume_p = uu____783;
                            FStar_Syntax_Syntax.null_wp = uu____784;
                            FStar_Syntax_Syntax.trivial = uu____785;
                            FStar_Syntax_Syntax.repr = uu____786;
                            FStar_Syntax_Syntax.return_repr = uu____793;
                            FStar_Syntax_Syntax.bind_repr = uu____794;
                            FStar_Syntax_Syntax.actions = uu____795
                          }
                       in
                    let wp_with_fresh_result_type env1 mname signature1 =
                      let fail t =
                        let uu____835 =
                          let uu____836 =
                            let uu____839 =
                              FStar_TypeChecker_Err.unexpected_signature_for_monad
                                env1 mname t
                               in
                            (uu____839, (FStar_Ident.range_of_lid mname))  in
                          FStar_Errors.Error uu____836  in
                        Prims.raise uu____835  in
                      let uu____844 =
                        let uu____845 =
                          FStar_Syntax_Subst.compress signature1  in
                        uu____845.FStar_Syntax_Syntax.n  in
                      match uu____844 with
                      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                          let bs1 = FStar_Syntax_Subst.open_binders bs  in
                          (match bs1 with
                           | (a,uu____870)::(wp,uu____872)::[] ->
                               (a, (wp.FStar_Syntax_Syntax.sort))
                           | uu____881 -> fail signature1)
                      | uu____882 -> fail signature1  in
                    let uu____883 =
                      wp_with_fresh_result_type env
                        ed2.FStar_Syntax_Syntax.mname
                        ed2.FStar_Syntax_Syntax.signature
                       in
                    (match uu____883 with
                     | (a,wp_a) ->
                         let fresh_effect_signature uu____901 =
                           let uu____902 =
                             FStar_TypeChecker_TcTerm.tc_trivial_guard env
                               signature_un
                              in
                           match uu____902 with
                           | (signature1,uu____910) ->
                               wp_with_fresh_result_type env
                                 ed2.FStar_Syntax_Syntax.mname signature1
                            in
                         let env1 =
                           let uu____912 =
                             FStar_Syntax_Syntax.new_bv None
                               ed2.FStar_Syntax_Syntax.signature
                              in
                           FStar_TypeChecker_Env.push_bv env uu____912  in
                         ((let uu____914 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED")
                              in
                           if uu____914
                           then
                             let uu____915 =
                               FStar_Syntax_Print.lid_to_string
                                 ed2.FStar_Syntax_Syntax.mname
                                in
                             let uu____916 =
                               FStar_Syntax_Print.binders_to_string " "
                                 ed2.FStar_Syntax_Syntax.binders
                                in
                             let uu____917 =
                               FStar_Syntax_Print.term_to_string
                                 ed2.FStar_Syntax_Syntax.signature
                                in
                             let uu____918 =
                               let uu____919 =
                                 FStar_Syntax_Syntax.bv_to_name a  in
                               FStar_Syntax_Print.term_to_string uu____919
                                in
                             let uu____920 =
                               FStar_Syntax_Print.term_to_string
                                 a.FStar_Syntax_Syntax.sort
                                in
                             FStar_Util.print5
                               "Checking effect signature: %s %s : %s\n(a is %s:%s)\n"
                               uu____915 uu____916 uu____917 uu____918
                               uu____920
                           else ());
                          (let check_and_gen' env2 uu____933 k =
                             match uu____933 with
                             | (uu____938,t) -> check_and_gen env2 t k  in
                           let return_wp =
                             let expected_k =
                               let uu____944 =
                                 let uu____945 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____946 =
                                   let uu____948 =
                                     let uu____949 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____949
                                      in
                                   [uu____948]  in
                                 uu____945 :: uu____946  in
                               let uu____950 =
                                 FStar_Syntax_Syntax.mk_GTotal wp_a  in
                               FStar_Syntax_Util.arrow uu____944 uu____950
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ret_wp expected_k
                              in
                           let bind_wp =
                             let uu____952 = fresh_effect_signature ()  in
                             match uu____952 with
                             | (b,wp_b) ->
                                 let a_wp_b =
                                   let uu____964 =
                                     let uu____965 =
                                       let uu____966 =
                                         FStar_Syntax_Syntax.bv_to_name a  in
                                       FStar_Syntax_Syntax.null_binder
                                         uu____966
                                        in
                                     [uu____965]  in
                                   let uu____967 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____964
                                     uu____967
                                    in
                                 let expected_k =
                                   let uu____969 =
                                     let uu____970 =
                                       FStar_Syntax_Syntax.null_binder
                                         FStar_TypeChecker_Common.t_range
                                        in
                                     let uu____971 =
                                       let uu____973 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____974 =
                                         let uu____976 =
                                           FStar_Syntax_Syntax.mk_binder b
                                            in
                                         let uu____977 =
                                           let uu____979 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_a
                                              in
                                           let uu____980 =
                                             let uu____982 =
                                               FStar_Syntax_Syntax.null_binder
                                                 a_wp_b
                                                in
                                             [uu____982]  in
                                           uu____979 :: uu____980  in
                                         uu____976 :: uu____977  in
                                       uu____973 :: uu____974  in
                                     uu____970 :: uu____971  in
                                   let uu____983 =
                                     FStar_Syntax_Syntax.mk_Total wp_b  in
                                   FStar_Syntax_Util.arrow uu____969
                                     uu____983
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.bind_wp expected_k
                              in
                           let if_then_else1 =
                             let p =
                               let uu____986 =
                                 let uu____987 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____987 Prims.fst  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____986
                                in
                             let expected_k =
                               let uu____993 =
                                 let uu____994 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____995 =
                                   let uu____997 =
                                     FStar_Syntax_Syntax.mk_binder p  in
                                   let uu____998 =
                                     let uu____1000 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     let uu____1001 =
                                       let uu____1003 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____1003]  in
                                     uu____1000 :: uu____1001  in
                                   uu____997 :: uu____998  in
                                 uu____994 :: uu____995  in
                               let uu____1004 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____993 uu____1004
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.if_then_else
                               expected_k
                              in
                           let ite_wp =
                             let expected_k =
                               let uu____1007 =
                                 let uu____1008 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____1009 =
                                   let uu____1011 =
                                     FStar_Syntax_Syntax.null_binder wp_a  in
                                   [uu____1011]  in
                                 uu____1008 :: uu____1009  in
                               let uu____1012 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____1007 uu____1012
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.ite_wp expected_k
                              in
                           let stronger =
                             let uu____1014 = FStar_Syntax_Util.type_u ()  in
                             match uu____1014 with
                             | (t,uu____1018) ->
                                 let expected_k =
                                   let uu____1020 =
                                     let uu____1021 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____1022 =
                                       let uu____1024 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       let uu____1025 =
                                         let uu____1027 =
                                           FStar_Syntax_Syntax.null_binder
                                             wp_a
                                            in
                                         [uu____1027]  in
                                       uu____1024 :: uu____1025  in
                                     uu____1021 :: uu____1022  in
                                   let uu____1028 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   FStar_Syntax_Util.arrow uu____1020
                                     uu____1028
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.stronger
                                   expected_k
                              in
                           let close_wp =
                             let b =
                               let uu____1031 =
                                 let uu____1032 = FStar_Syntax_Util.type_u ()
                                    in
                                 FStar_All.pipe_right uu____1032 Prims.fst
                                  in
                               FStar_Syntax_Syntax.new_bv
                                 (Some
                                    (FStar_Ident.range_of_lid
                                       ed2.FStar_Syntax_Syntax.mname))
                                 uu____1031
                                in
                             let b_wp_a =
                               let uu____1038 =
                                 let uu____1039 =
                                   let uu____1040 =
                                     FStar_Syntax_Syntax.bv_to_name b  in
                                   FStar_Syntax_Syntax.null_binder uu____1040
                                    in
                                 [uu____1039]  in
                               let uu____1041 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____1038 uu____1041
                                in
                             let expected_k =
                               let uu____1043 =
                                 let uu____1044 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____1045 =
                                   let uu____1047 =
                                     FStar_Syntax_Syntax.mk_binder b  in
                                   let uu____1048 =
                                     let uu____1050 =
                                       FStar_Syntax_Syntax.null_binder b_wp_a
                                        in
                                     [uu____1050]  in
                                   uu____1047 :: uu____1048  in
                                 uu____1044 :: uu____1045  in
                               let uu____1051 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____1043 uu____1051
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.close_wp expected_k
                              in
                           let assert_p =
                             let expected_k =
                               let uu____1054 =
                                 let uu____1055 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____1056 =
                                   let uu____1058 =
                                     let uu____1059 =
                                       let uu____1060 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____1060
                                         Prims.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____1059
                                      in
                                   let uu____1065 =
                                     let uu____1067 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____1067]  in
                                   uu____1058 :: uu____1065  in
                                 uu____1055 :: uu____1056  in
                               let uu____1068 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____1054 uu____1068
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assert_p expected_k
                              in
                           let assume_p =
                             let expected_k =
                               let uu____1071 =
                                 let uu____1072 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 let uu____1073 =
                                   let uu____1075 =
                                     let uu____1076 =
                                       let uu____1077 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____1077
                                         Prims.fst
                                        in
                                     FStar_Syntax_Syntax.null_binder
                                       uu____1076
                                      in
                                   let uu____1082 =
                                     let uu____1084 =
                                       FStar_Syntax_Syntax.null_binder wp_a
                                        in
                                     [uu____1084]  in
                                   uu____1075 :: uu____1082  in
                                 uu____1072 :: uu____1073  in
                               let uu____1085 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____1071 uu____1085
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.assume_p expected_k
                              in
                           let null_wp =
                             let expected_k =
                               let uu____1088 =
                                 let uu____1089 =
                                   FStar_Syntax_Syntax.mk_binder a  in
                                 [uu____1089]  in
                               let uu____1090 =
                                 FStar_Syntax_Syntax.mk_Total wp_a  in
                               FStar_Syntax_Util.arrow uu____1088 uu____1090
                                in
                             check_and_gen' env1
                               ed2.FStar_Syntax_Syntax.null_wp expected_k
                              in
                           let trivial_wp =
                             let uu____1092 = FStar_Syntax_Util.type_u ()  in
                             match uu____1092 with
                             | (t,uu____1096) ->
                                 let expected_k =
                                   let uu____1098 =
                                     let uu____1099 =
                                       FStar_Syntax_Syntax.mk_binder a  in
                                     let uu____1100 =
                                       let uu____1102 =
                                         FStar_Syntax_Syntax.null_binder wp_a
                                          in
                                       [uu____1102]  in
                                     uu____1099 :: uu____1100  in
                                   let uu____1103 =
                                     FStar_Syntax_Syntax.mk_GTotal t  in
                                   FStar_Syntax_Util.arrow uu____1098
                                     uu____1103
                                    in
                                 check_and_gen' env1
                                   ed2.FStar_Syntax_Syntax.trivial expected_k
                              in
                           let uu____1104 =
                             let uu____1110 =
                               let uu____1111 =
                                 FStar_Syntax_Subst.compress
                                   ed2.FStar_Syntax_Syntax.repr
                                  in
                               uu____1111.FStar_Syntax_Syntax.n  in
                             match uu____1110 with
                             | FStar_Syntax_Syntax.Tm_unknown  ->
                                 ((ed2.FStar_Syntax_Syntax.repr),
                                   (ed2.FStar_Syntax_Syntax.bind_repr),
                                   (ed2.FStar_Syntax_Syntax.return_repr),
                                   (ed2.FStar_Syntax_Syntax.actions))
                             | uu____1120 ->
                                 let repr =
                                   let uu____1122 =
                                     FStar_Syntax_Util.type_u ()  in
                                   match uu____1122 with
                                   | (t,uu____1126) ->
                                       let expected_k =
                                         let uu____1128 =
                                           let uu____1129 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____1130 =
                                             let uu____1132 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_a
                                                in
                                             [uu____1132]  in
                                           uu____1129 :: uu____1130  in
                                         let uu____1133 =
                                           FStar_Syntax_Syntax.mk_GTotal t
                                            in
                                         FStar_Syntax_Util.arrow uu____1128
                                           uu____1133
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
                                   let uu____1144 =
                                     let uu____1147 =
                                       let uu____1148 =
                                         let uu____1158 =
                                           let uu____1160 =
                                             FStar_Syntax_Syntax.as_arg t  in
                                           let uu____1161 =
                                             let uu____1163 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____1163]  in
                                           uu____1160 :: uu____1161  in
                                         (repr1, uu____1158)  in
                                       FStar_Syntax_Syntax.Tm_app uu____1148
                                        in
                                     FStar_Syntax_Syntax.mk uu____1147  in
                                   uu____1144 None FStar_Range.dummyRange  in
                                 let mk_repr a1 wp =
                                   let uu____1182 =
                                     FStar_Syntax_Syntax.bv_to_name a1  in
                                   mk_repr' uu____1182 wp  in
                                 let destruct_repr t =
                                   let uu____1193 =
                                     let uu____1194 =
                                       FStar_Syntax_Subst.compress t  in
                                     uu____1194.FStar_Syntax_Syntax.n  in
                                   match uu____1193 with
                                   | FStar_Syntax_Syntax.Tm_app
                                       (uu____1203,(t1,uu____1205)::(wp,uu____1207)::[])
                                       -> (t1, wp)
                                   | uu____1241 ->
                                       failwith "Unexpected repr type"
                                    in
                                 let bind_repr =
                                   let r =
                                     let uu____1250 =
                                       FStar_Syntax_Syntax.lid_as_fv
                                         FStar_Syntax_Const.range_0
                                         FStar_Syntax_Syntax.Delta_constant
                                         None
                                        in
                                     FStar_All.pipe_right uu____1250
                                       FStar_Syntax_Syntax.fv_to_tm
                                      in
                                   let uu____1251 = fresh_effect_signature ()
                                      in
                                   match uu____1251 with
                                   | (b,wp_b) ->
                                       let a_wp_b =
                                         let uu____1263 =
                                           let uu____1264 =
                                             let uu____1265 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____1265
                                              in
                                           [uu____1264]  in
                                         let uu____1266 =
                                           FStar_Syntax_Syntax.mk_Total wp_b
                                            in
                                         FStar_Syntax_Util.arrow uu____1263
                                           uu____1266
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
                                         let uu____1270 =
                                           FStar_Syntax_Syntax.bv_to_name a
                                            in
                                         FStar_Syntax_Syntax.gen_bv "x_a"
                                           None uu____1270
                                          in
                                       let wp_g_x =
                                         let uu____1274 =
                                           let uu____1275 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               wp_g
                                              in
                                           let uu____1276 =
                                             let uu____1277 =
                                               let uu____1278 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               FStar_All.pipe_left
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1278
                                                in
                                             [uu____1277]  in
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             uu____1275 uu____1276
                                            in
                                         uu____1274 None
                                           FStar_Range.dummyRange
                                          in
                                       let res =
                                         let wp =
                                           let uu____1289 =
                                             let uu____1290 =
                                               let uu____1291 =
                                                 FStar_TypeChecker_Env.inst_tscheme
                                                   bind_wp
                                                  in
                                               FStar_All.pipe_right
                                                 uu____1291 Prims.snd
                                                in
                                             let uu____1296 =
                                               let uu____1297 =
                                                 let uu____1299 =
                                                   let uu____1301 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       a
                                                      in
                                                   let uu____1302 =
                                                     let uu____1304 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b
                                                        in
                                                     let uu____1305 =
                                                       let uu____1307 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           wp_f
                                                          in
                                                       let uu____1308 =
                                                         let uu____1310 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             wp_g
                                                            in
                                                         [uu____1310]  in
                                                       uu____1307 ::
                                                         uu____1308
                                                        in
                                                     uu____1304 :: uu____1305
                                                      in
                                                   uu____1301 :: uu____1302
                                                    in
                                                 r :: uu____1299  in
                                               FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg
                                                 uu____1297
                                                in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____1290 uu____1296
                                              in
                                           uu____1289 None
                                             FStar_Range.dummyRange
                                            in
                                         mk_repr b wp  in
                                       let expected_k =
                                         let uu____1316 =
                                           let uu____1317 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____1318 =
                                             let uu____1320 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b
                                                in
                                             let uu____1321 =
                                               let uu____1323 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_f
                                                  in
                                               let uu____1324 =
                                                 let uu____1326 =
                                                   let uu____1327 =
                                                     let uu____1328 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         wp_f
                                                        in
                                                     mk_repr a uu____1328  in
                                                   FStar_Syntax_Syntax.null_binder
                                                     uu____1327
                                                    in
                                                 let uu____1329 =
                                                   let uu____1331 =
                                                     FStar_Syntax_Syntax.mk_binder
                                                       wp_g
                                                      in
                                                   let uu____1332 =
                                                     let uu____1334 =
                                                       let uu____1335 =
                                                         let uu____1336 =
                                                           let uu____1337 =
                                                             FStar_Syntax_Syntax.mk_binder
                                                               x_a
                                                              in
                                                           [uu____1337]  in
                                                         let uu____1338 =
                                                           let uu____1339 =
                                                             mk_repr b wp_g_x
                                                              in
                                                           FStar_All.pipe_left
                                                             FStar_Syntax_Syntax.mk_Total
                                                             uu____1339
                                                            in
                                                         FStar_Syntax_Util.arrow
                                                           uu____1336
                                                           uu____1338
                                                          in
                                                       FStar_Syntax_Syntax.null_binder
                                                         uu____1335
                                                        in
                                                     [uu____1334]  in
                                                   uu____1331 :: uu____1332
                                                    in
                                                 uu____1326 :: uu____1329  in
                                               uu____1323 :: uu____1324  in
                                             uu____1320 :: uu____1321  in
                                           uu____1317 :: uu____1318  in
                                         let uu____1340 =
                                           FStar_Syntax_Syntax.mk_Total res
                                            in
                                         FStar_Syntax_Util.arrow uu____1316
                                           uu____1340
                                          in
                                       let uu____1341 =
                                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                           env1 expected_k
                                          in
                                       (match uu____1341 with
                                        | (expected_k1,uu____1346,uu____1347)
                                            ->
                                            let env2 =
                                              FStar_TypeChecker_Env.set_range
                                                env1
                                                (Prims.snd
                                                   ed2.FStar_Syntax_Syntax.bind_repr).FStar_Syntax_Syntax.pos
                                               in
                                            let env3 =
                                              let uu___94_1351 = env2  in
                                              {
                                                FStar_TypeChecker_Env.solver
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.solver);
                                                FStar_TypeChecker_Env.range =
                                                  (uu___94_1351.FStar_TypeChecker_Env.range);
                                                FStar_TypeChecker_Env.curmodule
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.curmodule);
                                                FStar_TypeChecker_Env.gamma =
                                                  (uu___94_1351.FStar_TypeChecker_Env.gamma);
                                                FStar_TypeChecker_Env.gamma_cache
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.gamma_cache);
                                                FStar_TypeChecker_Env.modules
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.modules);
                                                FStar_TypeChecker_Env.expected_typ
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.expected_typ);
                                                FStar_TypeChecker_Env.sigtab
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.sigtab);
                                                FStar_TypeChecker_Env.is_pattern
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.is_pattern);
                                                FStar_TypeChecker_Env.instantiate_imp
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.instantiate_imp);
                                                FStar_TypeChecker_Env.effects
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.effects);
                                                FStar_TypeChecker_Env.generalize
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.generalize);
                                                FStar_TypeChecker_Env.letrecs
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.letrecs);
                                                FStar_TypeChecker_Env.top_level
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.top_level);
                                                FStar_TypeChecker_Env.check_uvars
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.check_uvars);
                                                FStar_TypeChecker_Env.use_eq
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.use_eq);
                                                FStar_TypeChecker_Env.is_iface
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.is_iface);
                                                FStar_TypeChecker_Env.admit =
                                                  (uu___94_1351.FStar_TypeChecker_Env.admit);
                                                FStar_TypeChecker_Env.lax =
                                                  true;
                                                FStar_TypeChecker_Env.lax_universes
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.lax_universes);
                                                FStar_TypeChecker_Env.type_of
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.type_of);
                                                FStar_TypeChecker_Env.universe_of
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.universe_of);
                                                FStar_TypeChecker_Env.use_bv_sorts
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.use_bv_sorts);
                                                FStar_TypeChecker_Env.qname_and_index
                                                  =
                                                  (uu___94_1351.FStar_TypeChecker_Env.qname_and_index)
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
                                     let uu____1358 =
                                       FStar_Syntax_Syntax.bv_to_name a  in
                                     FStar_Syntax_Syntax.gen_bv "x_a" None
                                       uu____1358
                                      in
                                   let res =
                                     let wp =
                                       let uu____1365 =
                                         let uu____1366 =
                                           let uu____1367 =
                                             FStar_TypeChecker_Env.inst_tscheme
                                               return_wp
                                              in
                                           FStar_All.pipe_right uu____1367
                                             Prims.snd
                                            in
                                         let uu____1372 =
                                           let uu____1373 =
                                             let uu____1375 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 a
                                                in
                                             let uu____1376 =
                                               let uu____1378 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   x_a
                                                  in
                                               [uu____1378]  in
                                             uu____1375 :: uu____1376  in
                                           FStar_List.map
                                             FStar_Syntax_Syntax.as_arg
                                             uu____1373
                                            in
                                         FStar_Syntax_Syntax.mk_Tm_app
                                           uu____1366 uu____1372
                                          in
                                       uu____1365 None FStar_Range.dummyRange
                                        in
                                     mk_repr a wp  in
                                   let expected_k =
                                     let uu____1384 =
                                       let uu____1385 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____1386 =
                                         let uu____1388 =
                                           FStar_Syntax_Syntax.mk_binder x_a
                                            in
                                         [uu____1388]  in
                                       uu____1385 :: uu____1386  in
                                     let uu____1389 =
                                       FStar_Syntax_Syntax.mk_Total res  in
                                     FStar_Syntax_Util.arrow uu____1384
                                       uu____1389
                                      in
                                   let uu____1390 =
                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                       env1 expected_k
                                      in
                                   match uu____1390 with
                                   | (expected_k1,uu____1398,uu____1399) ->
                                       let env2 =
                                         FStar_TypeChecker_Env.set_range env1
                                           (Prims.snd
                                              ed2.FStar_Syntax_Syntax.return_repr).FStar_Syntax_Syntax.pos
                                          in
                                       let uu____1402 =
                                         check_and_gen' env2
                                           ed2.FStar_Syntax_Syntax.return_repr
                                           expected_k1
                                          in
                                       (match uu____1402 with
                                        | (univs1,repr1) ->
                                            (match univs1 with
                                             | [] -> ([], repr1)
                                             | uu____1414 ->
                                                 Prims.raise
                                                   (FStar_Errors.Error
                                                      ("Unexpected universe-polymorphic return for effect",
                                                        (repr1.FStar_Syntax_Syntax.pos)))))
                                    in
                                 let actions =
                                   let check_action act =
                                     let uu____1425 =
                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                         env1
                                         act.FStar_Syntax_Syntax.action_typ
                                        in
                                     match uu____1425 with
                                     | (act_typ,uu____1430,g_t) ->
                                         let env' =
                                           FStar_TypeChecker_Env.set_expected_typ
                                             env1 act_typ
                                            in
                                         ((let uu____1434 =
                                             FStar_TypeChecker_Env.debug env1
                                               (FStar_Options.Other "ED")
                                              in
                                           if uu____1434
                                           then
                                             let uu____1435 =
                                               FStar_Syntax_Print.term_to_string
                                                 act.FStar_Syntax_Syntax.action_defn
                                                in
                                             let uu____1436 =
                                               FStar_Syntax_Print.term_to_string
                                                 act_typ
                                                in
                                             FStar_Util.print3
                                               "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                               (FStar_Ident.text_of_lid
                                                  act.FStar_Syntax_Syntax.action_name)
                                               uu____1435 uu____1436
                                           else ());
                                          (let uu____1438 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env'
                                               act.FStar_Syntax_Syntax.action_defn
                                              in
                                           match uu____1438 with
                                           | (act_defn,uu____1443,g_a) ->
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
                                               let uu____1447 =
                                                 let act_typ2 =
                                                   FStar_Syntax_Subst.compress
                                                     act_typ1
                                                    in
                                                 match act_typ2.FStar_Syntax_Syntax.n
                                                 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs,c) ->
                                                     let uu____1465 =
                                                       FStar_Syntax_Subst.open_comp
                                                         bs c
                                                        in
                                                     (match uu____1465 with
                                                      | (bs1,uu____1471) ->
                                                          let res =
                                                            mk_repr'
                                                              FStar_Syntax_Syntax.tun
                                                              FStar_Syntax_Syntax.tun
                                                             in
                                                          let k =
                                                            let uu____1476 =
                                                              FStar_Syntax_Syntax.mk_Total
                                                                res
                                                               in
                                                            FStar_Syntax_Util.arrow
                                                              bs1 uu____1476
                                                             in
                                                          let uu____1477 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env1 k
                                                             in
                                                          (match uu____1477
                                                           with
                                                           | (k1,uu____1484,g)
                                                               -> (k1, g)))
                                                 | uu____1486 ->
                                                     let uu____1487 =
                                                       let uu____1488 =
                                                         let uu____1491 =
                                                           let uu____1492 =
                                                             FStar_Syntax_Print.term_to_string
                                                               act_typ2
                                                              in
                                                           let uu____1493 =
                                                             FStar_Syntax_Print.tag_of_term
                                                               act_typ2
                                                              in
                                                           FStar_Util.format2
                                                             "Actions must have function types (not: %s, a.k.a. %s)"
                                                             uu____1492
                                                             uu____1493
                                                            in
                                                         (uu____1491,
                                                           (act_defn1.FStar_Syntax_Syntax.pos))
                                                          in
                                                       FStar_Errors.Error
                                                         uu____1488
                                                        in
                                                     Prims.raise uu____1487
                                                  in
                                               (match uu____1447 with
                                                | (expected_k,g_k) ->
                                                    let g =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 act_typ1
                                                        expected_k
                                                       in
                                                    ((let uu____1500 =
                                                        let uu____1501 =
                                                          let uu____1502 =
                                                            FStar_TypeChecker_Rel.conj_guard
                                                              g_t g
                                                             in
                                                          FStar_TypeChecker_Rel.conj_guard
                                                            g_k uu____1502
                                                           in
                                                        FStar_TypeChecker_Rel.conj_guard
                                                          g_a uu____1501
                                                         in
                                                      FStar_TypeChecker_Rel.force_trivial_guard
                                                        env1 uu____1500);
                                                     (let act_typ2 =
                                                        let uu____1504 =
                                                          let uu____1505 =
                                                            FStar_Syntax_Subst.compress
                                                              expected_k
                                                             in
                                                          uu____1505.FStar_Syntax_Syntax.n
                                                           in
                                                        match uu____1504 with
                                                        | FStar_Syntax_Syntax.Tm_arrow
                                                            (bs,c) ->
                                                            let uu____1520 =
                                                              FStar_Syntax_Subst.open_comp
                                                                bs c
                                                               in
                                                            (match uu____1520
                                                             with
                                                             | (bs1,c1) ->
                                                                 let uu____1525
                                                                   =
                                                                   let uu____1532
                                                                    =
                                                                    FStar_TypeChecker_Env.result_typ
                                                                    env1 c1
                                                                     in
                                                                   destruct_repr
                                                                    uu____1532
                                                                    in
                                                                 (match uu____1525
                                                                  with
                                                                  | (a1,wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____1544
                                                                    =
                                                                    let uu____1545
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a1
                                                                     in
                                                                    [uu____1545]
                                                                     in
                                                                    let uu____1546
                                                                    =
                                                                    let uu____1552
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    a1  in
                                                                    let uu____1553
                                                                    =
                                                                    let uu____1555
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____1555]
                                                                     in
                                                                    uu____1552
                                                                    ::
                                                                    uu____1553
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_typ_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____1544;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____1546;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____1556
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs1
                                                                    uu____1556))
                                                        | uu____1557 ->
                                                            failwith ""
                                                         in
                                                      let uu____1558 =
                                                        FStar_TypeChecker_Util.generalize_universes
                                                          env1 act_defn1
                                                         in
                                                      match uu____1558 with
                                                      | (univs1,act_defn2) ->
                                                          let act_typ3 =
                                                            FStar_TypeChecker_Normalize.normalize
                                                              [FStar_TypeChecker_Normalize.Beta]
                                                              env1 act_typ2
                                                             in
                                                          let uu___95_1564 =
                                                            act  in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___95_1564.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___95_1564.FStar_Syntax_Syntax.action_unqualified_name);
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
                           match uu____1104 with
                           | (repr,bind_repr,return_repr,actions) ->
                               let t =
                                 FStar_Syntax_Util.maybe_tot_arrow
                                   ed2.FStar_Syntax_Syntax.binders
                                   ed2.FStar_Syntax_Syntax.signature
                                  in
                               let uu____1578 =
                                 FStar_TypeChecker_Util.generalize_universes
                                   env0 t
                                  in
                               (match uu____1578 with
                                | (univs1,t1) ->
                                    let signature1 =
                                      let uu____1584 =
                                        let uu____1587 =
                                          let uu____1588 =
                                            FStar_Syntax_Subst.compress t1
                                             in
                                          uu____1588.FStar_Syntax_Syntax.n
                                           in
                                        (effect_params, uu____1587)  in
                                      match uu____1584 with
                                      | ([],uu____1591) -> t1
                                      | (uu____1597,FStar_Syntax_Syntax.Tm_arrow
                                         (uu____1598,c)) ->
                                          FStar_TypeChecker_Env.result_typ
                                            env0 c
                                      | uu____1610 -> failwith "Impossible"
                                       in
                                    let close1 n1 ts =
                                      let ts1 =
                                        let uu____1621 =
                                          FStar_Syntax_Subst.close_tscheme
                                            effect_params ts
                                           in
                                        FStar_Syntax_Subst.close_univ_vars_tscheme
                                          univs1 uu____1621
                                         in
                                      let m =
                                        FStar_List.length (Prims.fst ts1)  in
                                      (let uu____1626 =
                                         ((n1 >= (Prims.parse_int "0")) &&
                                            (let uu____1627 =
                                               FStar_Syntax_Util.is_unknown
                                                 (Prims.snd ts1)
                                                in
                                             Prims.op_Negation uu____1627))
                                           && (m <> n1)
                                          in
                                       if uu____1626
                                       then
                                         let error =
                                           if m < n1
                                           then
                                             "not universe-polymorphic enough"
                                           else "too universe-polymorphic"
                                            in
                                         let uu____1636 =
                                           let uu____1637 =
                                             FStar_Util.string_of_int n1  in
                                           let uu____1638 =
                                             FStar_Syntax_Print.tscheme_to_string
                                               ts1
                                              in
                                           FStar_Util.format3
                                             "The effect combinator is %s (n=%s) (%s)"
                                             error uu____1637 uu____1638
                                            in
                                         failwith uu____1636
                                       else ());
                                      ts1  in
                                    let close_action act =
                                      let uu____1644 =
                                        close1 (~- (Prims.parse_int "1"))
                                          ((act.FStar_Syntax_Syntax.action_univs),
                                            (act.FStar_Syntax_Syntax.action_defn))
                                         in
                                      match uu____1644 with
                                      | (univs2,defn) ->
                                          let uu____1649 =
                                            close1 (~- (Prims.parse_int "1"))
                                              ((act.FStar_Syntax_Syntax.action_univs),
                                                (act.FStar_Syntax_Syntax.action_typ))
                                             in
                                          (match uu____1649 with
                                           | (univs',typ) ->
                                               let uu___96_1655 = act  in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___96_1655.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___96_1655.FStar_Syntax_Syntax.action_unqualified_name);
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
                                      let uu___97_1660 = ed2  in
                                      let uu____1661 =
                                        close1 (Prims.parse_int "0")
                                          return_wp
                                         in
                                      let uu____1662 =
                                        close1 (Prims.parse_int "1") bind_wp
                                         in
                                      let uu____1663 =
                                        close1 (Prims.parse_int "0")
                                          if_then_else1
                                         in
                                      let uu____1664 =
                                        close1 (Prims.parse_int "0") ite_wp
                                         in
                                      let uu____1665 =
                                        close1 (Prims.parse_int "0") stronger
                                         in
                                      let uu____1666 =
                                        close1 (Prims.parse_int "1") close_wp
                                         in
                                      let uu____1667 =
                                        close1 (Prims.parse_int "0") assert_p
                                         in
                                      let uu____1668 =
                                        close1 (Prims.parse_int "0") assume_p
                                         in
                                      let uu____1669 =
                                        close1 (Prims.parse_int "0") null_wp
                                         in
                                      let uu____1670 =
                                        close1 (Prims.parse_int "0")
                                          trivial_wp
                                         in
                                      let uu____1671 =
                                        let uu____1672 =
                                          close1 (Prims.parse_int "0")
                                            ([], repr)
                                           in
                                        Prims.snd uu____1672  in
                                      let uu____1678 =
                                        close1 (Prims.parse_int "0")
                                          return_repr
                                         in
                                      let uu____1679 =
                                        close1 (Prims.parse_int "1")
                                          bind_repr
                                         in
                                      let uu____1680 =
                                        FStar_List.map close_action actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.qualifiers =
                                          (uu___97_1660.FStar_Syntax_Syntax.qualifiers);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___97_1660.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.mname =
                                          (uu___97_1660.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.univs = univs1;
                                        FStar_Syntax_Syntax.binders =
                                          effect_params;
                                        FStar_Syntax_Syntax.signature =
                                          signature1;
                                        FStar_Syntax_Syntax.ret_wp =
                                          uu____1661;
                                        FStar_Syntax_Syntax.bind_wp =
                                          uu____1662;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____1663;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____1664;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____1665;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____1666;
                                        FStar_Syntax_Syntax.assert_p =
                                          uu____1667;
                                        FStar_Syntax_Syntax.assume_p =
                                          uu____1668;
                                        FStar_Syntax_Syntax.null_wp =
                                          uu____1669;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____1670;
                                        FStar_Syntax_Syntax.repr = uu____1671;
                                        FStar_Syntax_Syntax.return_repr =
                                          uu____1678;
                                        FStar_Syntax_Syntax.bind_repr =
                                          uu____1679;
                                        FStar_Syntax_Syntax.actions =
                                          uu____1680
                                      }  in
                                    ((let uu____1683 =
                                        (FStar_TypeChecker_Env.debug env1
                                           FStar_Options.Low)
                                          ||
                                          (FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other "ED"))
                                         in
                                      if uu____1683
                                      then
                                        let uu____1684 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print_string uu____1684
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
      let uu____1688 =
        FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders
          ed.FStar_Syntax_Syntax.signature
         in
      match uu____1688 with
      | (effect_binders_un,signature_un) ->
          let uu____1698 =
            FStar_TypeChecker_TcTerm.tc_tparams env effect_binders_un  in
          (match uu____1698 with
           | (effect_binders,env1,uu____1709) ->
               let uu____1710 =
                 FStar_TypeChecker_TcTerm.tc_trivial_guard env1 signature_un
                  in
               (match uu____1710 with
                | (signature,uu____1719) ->
                    let effect_binders1 =
                      FStar_List.map
                        (fun uu____1728  ->
                           match uu____1728 with
                           | (bv,qual) ->
                               let uu____1735 =
                                 let uu___98_1736 = bv  in
                                 let uu____1737 =
                                   FStar_TypeChecker_Normalize.normalize
                                     [FStar_TypeChecker_Normalize.EraseUniverses]
                                     env1 bv.FStar_Syntax_Syntax.sort
                                    in
                                 {
                                   FStar_Syntax_Syntax.ppname =
                                     (uu___98_1736.FStar_Syntax_Syntax.ppname);
                                   FStar_Syntax_Syntax.index =
                                     (uu___98_1736.FStar_Syntax_Syntax.index);
                                   FStar_Syntax_Syntax.sort = uu____1737
                                 }  in
                               (uu____1735, qual)) effect_binders
                       in
                    let uu____1740 =
                      let uu____1745 =
                        let uu____1746 =
                          FStar_Syntax_Subst.compress signature_un  in
                        uu____1746.FStar_Syntax_Syntax.n  in
                      match uu____1745 with
                      | FStar_Syntax_Syntax.Tm_arrow
                          ((a,uu____1754)::[],effect_marker) ->
                          (a, effect_marker)
                      | uu____1769 ->
                          failwith "bad shape for effect-for-free signature"
                       in
                    (match uu____1740 with
                     | (a,effect_marker) ->
                         let a1 =
                           let uu____1786 = FStar_Syntax_Syntax.is_null_bv a
                              in
                           if uu____1786
                           then
                             let uu____1787 =
                               let uu____1789 =
                                 FStar_Syntax_Syntax.range_of_bv a  in
                               Some uu____1789  in
                             FStar_Syntax_Syntax.gen_bv "a" uu____1787
                               a.FStar_Syntax_Syntax.sort
                           else a  in
                         let open_and_check t =
                           let subst1 =
                             FStar_Syntax_Subst.opening_of_binders
                               effect_binders1
                              in
                           let t1 = FStar_Syntax_Subst.subst subst1 t  in
                           let uu____1799 =
                             FStar_TypeChecker_TcTerm.tc_term env1 t1  in
                           match uu____1799 with
                           | (t2,comp,uu____1807) -> (t2, comp)  in
                         let mk1 x =
                           FStar_Syntax_Syntax.mk x None
                             signature.FStar_Syntax_Syntax.pos
                            in
                         let uu____1818 =
                           open_and_check ed.FStar_Syntax_Syntax.repr  in
                         (match uu____1818 with
                          | (repr,_comp) ->
                              ((let uu____1829 =
                                  FStar_TypeChecker_Env.debug env1
                                    (FStar_Options.Other "ED")
                                   in
                                if uu____1829
                                then
                                  let uu____1830 =
                                    FStar_Syntax_Print.term_to_string repr
                                     in
                                  FStar_Util.print1 "Representation is: %s\n"
                                    uu____1830
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
                                  let uu____1836 =
                                    let uu____1837 =
                                      let uu____1838 =
                                        let uu____1848 =
                                          let uu____1852 =
                                            let uu____1855 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a1
                                               in
                                            let uu____1856 =
                                              FStar_Syntax_Syntax.as_implicit
                                                false
                                               in
                                            (uu____1855, uu____1856)  in
                                          [uu____1852]  in
                                        (wp_type1, uu____1848)  in
                                      FStar_Syntax_Syntax.Tm_app uu____1838
                                       in
                                    mk1 uu____1837  in
                                  FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Normalize.Beta] env1
                                    uu____1836
                                   in
                                let effect_signature =
                                  let binders =
                                    let uu____1871 =
                                      let uu____1874 =
                                        FStar_Syntax_Syntax.as_implicit false
                                         in
                                      (a1, uu____1874)  in
                                    let uu____1875 =
                                      let uu____1879 =
                                        let uu____1880 =
                                          FStar_Syntax_Syntax.gen_bv
                                            "dijkstra_wp" None wp_a
                                           in
                                        FStar_All.pipe_right uu____1880
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      [uu____1879]  in
                                    uu____1871 :: uu____1875  in
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
                                  let uu____1913 = item  in
                                  match uu____1913 with
                                  | (u_item,item1) ->
                                      let uu____1925 = open_and_check item1
                                         in
                                      (match uu____1925 with
                                       | (item2,item_comp) ->
                                           ((let uu____1935 =
                                               let uu____1936 =
                                                 FStar_Syntax_Util.is_total_lcomp
                                                   item_comp
                                                  in
                                               Prims.op_Negation uu____1936
                                                in
                                             if uu____1935
                                             then
                                               let uu____1937 =
                                                 let uu____1938 =
                                                   let uu____1939 =
                                                     FStar_Syntax_Print.term_to_string
                                                       item2
                                                      in
                                                   let uu____1940 =
                                                     FStar_Syntax_Print.lcomp_to_string
                                                       item_comp
                                                      in
                                                   FStar_Util.format2
                                                     "Computation for [%s] is not total : %s !"
                                                     uu____1939 uu____1940
                                                    in
                                                 FStar_Errors.Err uu____1938
                                                  in
                                               Prims.raise uu____1937
                                             else ());
                                            (let uu____1942 =
                                               FStar_TypeChecker_DMFF.star_expr
                                                 dmff_env1 item2
                                                in
                                             match uu____1942 with
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
                                let uu____1955 =
                                  elaborate_and_star dmff_env
                                    ed.FStar_Syntax_Syntax.bind_repr
                                   in
                                match uu____1955 with
                                | (dmff_env1,uu____1966,bind_wp,bind_elab) ->
                                    let uu____1969 =
                                      elaborate_and_star dmff_env1
                                        ed.FStar_Syntax_Syntax.return_repr
                                       in
                                    (match uu____1969 with
                                     | (dmff_env2,uu____1980,return_wp,return_elab)
                                         ->
                                         let lift_from_pure_wp =
                                           let uu____1984 =
                                             let uu____1985 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____1985.FStar_Syntax_Syntax.n
                                              in
                                           match uu____1984 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2023 =
                                                 let uu____2031 =
                                                   let uu____2034 =
                                                     FStar_Syntax_Util.abs bs
                                                       body None
                                                      in
                                                   FStar_Syntax_Subst.open_term
                                                     [b1; b2] uu____2034
                                                    in
                                                 match uu____2031 with
                                                 | (b11::b21::[],body1) ->
                                                     (b11, b21, body1)
                                                 | uu____2073 ->
                                                     failwith
                                                       "Impossible : open_term not preserving binders arity"
                                                  in
                                               (match uu____2023 with
                                                | (b11,b21,body1) ->
                                                    let env0 =
                                                      let uu____2095 =
                                                        FStar_TypeChecker_DMFF.get_env
                                                          dmff_env2
                                                         in
                                                      FStar_TypeChecker_Env.push_binders
                                                        uu____2095 [b11; b21]
                                                       in
                                                    let wp_b1 =
                                                      let uu____2103 =
                                                        let uu____2104 =
                                                          let uu____2105 =
                                                            let uu____2115 =
                                                              let uu____2119
                                                                =
                                                                let uu____2122
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    (
                                                                    Prims.fst
                                                                    b11)
                                                                   in
                                                                let uu____2123
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2122,
                                                                  uu____2123)
                                                                 in
                                                              [uu____2119]
                                                               in
                                                            (wp_type1,
                                                              uu____2115)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2105
                                                           in
                                                        mk1 uu____2104  in
                                                      FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Normalize.Beta]
                                                        env0 uu____2103
                                                       in
                                                    let uu____2131 =
                                                      let uu____2141 =
                                                        let uu____2142 =
                                                          FStar_Syntax_Util.unascribe
                                                            wp_b1
                                                           in
                                                        FStar_TypeChecker_Normalize.eta_expand_with_type
                                                          env0 body1
                                                          uu____2142
                                                         in
                                                      FStar_All.pipe_left
                                                        FStar_Syntax_Util.abs_formals
                                                        uu____2141
                                                       in
                                                    (match uu____2131 with
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
                                                           let uu____2175 =
                                                             let uu____2176 =
                                                               FStar_Syntax_Syntax.bv_to_name
                                                                 wp
                                                                in
                                                             let uu____2177 =
                                                               let uu____2178
                                                                 =
                                                                 let uu____2182
                                                                   =
                                                                   FStar_Syntax_Util.abs
                                                                    [b21]
                                                                    body2
                                                                    what'
                                                                    in
                                                                 (uu____2182,
                                                                   None)
                                                                  in
                                                               [uu____2178]
                                                                in
                                                             FStar_Syntax_Syntax.mk_Tm_app
                                                               uu____2176
                                                               uu____2177
                                                              in
                                                           uu____2175 None
                                                             FStar_Range.dummyRange
                                                            in
                                                         let uu____2198 =
                                                           let uu____2202 =
                                                             let uu____2206 =
                                                               FStar_Syntax_Syntax.mk_binder
                                                                 wp
                                                                in
                                                             [uu____2206]  in
                                                           b11 :: uu____2202
                                                            in
                                                         let uu____2209 =
                                                           FStar_Syntax_Util.abs
                                                             bs1 body3 what
                                                            in
                                                         FStar_Syntax_Util.abs
                                                           uu____2198
                                                           uu____2209
                                                           (Some
                                                              (FStar_Util.Inr
                                                                 (FStar_Syntax_Const.effect_GTot_lid,
                                                                   [])))))
                                           | uu____2219 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let return_wp1 =
                                           let uu____2221 =
                                             let uu____2222 =
                                               FStar_Syntax_Subst.compress
                                                 return_wp
                                                in
                                             uu____2222.FStar_Syntax_Syntax.n
                                              in
                                           match uu____2221 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (b1::b2::bs,body,what) ->
                                               let uu____2260 =
                                                 FStar_Syntax_Util.abs bs
                                                   body what
                                                  in
                                               FStar_Syntax_Util.abs 
                                                 [b1; b2] uu____2260
                                                 (Some
                                                    (FStar_Util.Inr
                                                       (FStar_Syntax_Const.effect_GTot_lid,
                                                         [])))
                                           | uu____2276 ->
                                               failwith
                                                 "unexpected shape for return"
                                            in
                                         let bind_wp1 =
                                           let uu____2278 =
                                             let uu____2279 =
                                               FStar_Syntax_Subst.compress
                                                 bind_wp
                                                in
                                             uu____2279.FStar_Syntax_Syntax.n
                                              in
                                           match uu____2278 with
                                           | FStar_Syntax_Syntax.Tm_abs
                                               (binders,body,what) ->
                                               let r =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Syntax_Const.range_lid
                                                   (FStar_Syntax_Syntax.Delta_defined_at_level
                                                      (Prims.parse_int "1"))
                                                   None
                                                  in
                                               let uu____2308 =
                                                 let uu____2312 =
                                                   let uu____2314 =
                                                     let uu____2315 =
                                                       mk1
                                                         (FStar_Syntax_Syntax.Tm_fvar
                                                            r)
                                                        in
                                                     FStar_Syntax_Syntax.null_binder
                                                       uu____2315
                                                      in
                                                   [uu____2314]  in
                                                 FStar_List.append uu____2312
                                                   binders
                                                  in
                                               FStar_Syntax_Util.abs
                                                 uu____2308 body what
                                           | uu____2316 ->
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
                                             (let uu____2334 =
                                                let uu____2335 =
                                                  let uu____2336 =
                                                    let uu____2346 =
                                                      let uu____2347 =
                                                        FStar_Syntax_Util.args_of_binders
                                                          effect_binders1
                                                         in
                                                      Prims.snd uu____2347
                                                       in
                                                    (t, uu____2346)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____2336
                                                   in
                                                mk1 uu____2335  in
                                              FStar_Syntax_Subst.close
                                                effect_binders1 uu____2334)
                                            in
                                         let register name item =
                                           let uu____2359 =
                                             let uu____2362 = mk_lid name  in
                                             let uu____2363 =
                                               FStar_Syntax_Util.abs
                                                 effect_binders1 item None
                                                in
                                             FStar_TypeChecker_Util.mk_toplevel_definition
                                               env1 uu____2362 uu____2363
                                              in
                                           match uu____2359 with
                                           | (sigelt,fv) ->
                                               ((let uu____2372 =
                                                   let uu____2374 =
                                                     FStar_ST.read sigelts
                                                      in
                                                   sigelt :: uu____2374  in
                                                 FStar_ST.write sigelts
                                                   uu____2372);
                                                fv)
                                            in
                                         let lift_from_pure_wp1 =
                                           register "lift_from_pure"
                                             lift_from_pure_wp
                                            in
                                         let return_wp2 =
                                           register "return_wp" return_wp1
                                            in
                                         ((let uu____2385 =
                                             let uu____2387 =
                                               FStar_ST.read sigelts  in
                                             (FStar_Syntax_Syntax.Sig_pragma
                                                ((FStar_Syntax_Syntax.SetOptions
                                                    "--admit_smt_queries true"),
                                                  FStar_Range.dummyRange))
                                               :: uu____2387
                                              in
                                           FStar_ST.write sigelts uu____2385);
                                          (let return_elab1 =
                                             register "return_elab"
                                               return_elab
                                              in
                                           (let uu____2397 =
                                              let uu____2399 =
                                                FStar_ST.read sigelts  in
                                              (FStar_Syntax_Syntax.Sig_pragma
                                                 ((FStar_Syntax_Syntax.SetOptions
                                                     "--admit_smt_queries false"),
                                                   FStar_Range.dummyRange))
                                                :: uu____2399
                                               in
                                            FStar_ST.write sigelts uu____2397);
                                           (let bind_wp2 =
                                              register "bind_wp" bind_wp1  in
                                            (let uu____2409 =
                                               let uu____2411 =
                                                 FStar_ST.read sigelts  in
                                               (FStar_Syntax_Syntax.Sig_pragma
                                                  ((FStar_Syntax_Syntax.SetOptions
                                                      "--admit_smt_queries true"),
                                                    FStar_Range.dummyRange))
                                                 :: uu____2411
                                                in
                                             FStar_ST.write sigelts
                                               uu____2409);
                                            (let bind_elab1 =
                                               register "bind_elab" bind_elab
                                                in
                                             (let uu____2421 =
                                                let uu____2423 =
                                                  FStar_ST.read sigelts  in
                                                (FStar_Syntax_Syntax.Sig_pragma
                                                   ((FStar_Syntax_Syntax.SetOptions
                                                       "--admit_smt_queries false"),
                                                     FStar_Range.dummyRange))
                                                  :: uu____2423
                                                 in
                                              FStar_ST.write sigelts
                                                uu____2421);
                                             (let uu____2431 =
                                                FStar_List.fold_left
                                                  (fun uu____2438  ->
                                                     fun action  ->
                                                       match uu____2438 with
                                                       | (dmff_env3,actions)
                                                           ->
                                                           let uu____2450 =
                                                             elaborate_and_star
                                                               dmff_env3
                                                               ((action.FStar_Syntax_Syntax.action_univs),
                                                                 (action.FStar_Syntax_Syntax.action_defn))
                                                              in
                                                           (match uu____2450
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
                                                                let uu____2466
                                                                  =
                                                                  let uu____2468
                                                                    =
                                                                    let uu___99_2469
                                                                    = action
                                                                     in
                                                                    let uu____2470
                                                                    =
                                                                    apply_close
                                                                    action_elab1
                                                                     in
                                                                    let uu____2471
                                                                    =
                                                                    apply_close
                                                                    action_typ_with_wp1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___99_2469.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___99_2469.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    =
                                                                    (uu___99_2469.FStar_Syntax_Syntax.action_univs);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    uu____2470;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    uu____2471
                                                                    }  in
                                                                  uu____2468
                                                                    ::
                                                                    actions
                                                                   in
                                                                (dmff_env4,
                                                                  uu____2466)))
                                                  (dmff_env2, [])
                                                  ed.FStar_Syntax_Syntax.actions
                                                 in
                                              match uu____2431 with
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
                                                      let uu____2489 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          a1
                                                         in
                                                      let uu____2490 =
                                                        let uu____2492 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            wp
                                                           in
                                                        [uu____2492]  in
                                                      uu____2489 ::
                                                        uu____2490
                                                       in
                                                    let uu____2493 =
                                                      let uu____2494 =
                                                        let uu____2495 =
                                                          let uu____2496 =
                                                            let uu____2506 =
                                                              let uu____2510
                                                                =
                                                                let uu____2513
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a1
                                                                   in
                                                                let uu____2514
                                                                  =
                                                                  FStar_Syntax_Syntax.as_implicit
                                                                    false
                                                                   in
                                                                (uu____2513,
                                                                  uu____2514)
                                                                 in
                                                              [uu____2510]
                                                               in
                                                            (repr,
                                                              uu____2506)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_app
                                                            uu____2496
                                                           in
                                                        mk1 uu____2495  in
                                                      let uu____2522 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp
                                                         in
                                                      FStar_TypeChecker_DMFF.trans_F
                                                        dmff_env3 uu____2494
                                                        uu____2522
                                                       in
                                                    FStar_Syntax_Util.abs
                                                      binders uu____2493 None
                                                     in
                                                  let repr2 =
                                                    recheck_debug "FC" env1
                                                      repr1
                                                     in
                                                  let repr3 =
                                                    register "repr" repr2  in
                                                  let uu____2530 =
                                                    let uu____2533 =
                                                      let uu____2534 =
                                                        let uu____2537 =
                                                          FStar_Syntax_Subst.compress
                                                            wp_type1
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.unascribe
                                                          uu____2537
                                                         in
                                                      uu____2534.FStar_Syntax_Syntax.n
                                                       in
                                                    match uu____2533 with
                                                    | FStar_Syntax_Syntax.Tm_abs
                                                        (type_param::effect_param,arrow1,uu____2543)
                                                        ->
                                                        let uu____2570 =
                                                          let uu____2579 =
                                                            FStar_Syntax_Subst.open_term
                                                              (type_param ::
                                                              effect_param)
                                                              arrow1
                                                             in
                                                          match uu____2579
                                                          with
                                                          | (b::bs,body) ->
                                                              (b, bs, body)
                                                          | uu____2610 ->
                                                              failwith
                                                                "Impossible : open_term nt preserving binders arity"
                                                           in
                                                        (match uu____2570
                                                         with
                                                         | (type_param1,effect_param1,arrow2)
                                                             ->
                                                             let uu____2636 =
                                                               let uu____2637
                                                                 =
                                                                 let uu____2640
                                                                   =
                                                                   FStar_Syntax_Subst.compress
                                                                    arrow2
                                                                    in
                                                                 FStar_All.pipe_left
                                                                   FStar_Syntax_Util.unascribe
                                                                   uu____2640
                                                                  in
                                                               uu____2637.FStar_Syntax_Syntax.n
                                                                in
                                                             (match uu____2636
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_arrow
                                                                  (wp_binders,c)
                                                                  ->
                                                                  let uu____2655
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    wp_binders
                                                                    c  in
                                                                  (match uu____2655
                                                                   with
                                                                   | 
                                                                   (wp_binders1,c1)
                                                                    ->
                                                                    let uu____2662
                                                                    =
                                                                    FStar_List.partition
                                                                    (fun
                                                                    uu____2673
                                                                     ->
                                                                    match uu____2673
                                                                    with
                                                                    | 
                                                                    (bv,uu____2677)
                                                                    ->
                                                                    let uu____2678
                                                                    =
                                                                    let uu____2679
                                                                    =
                                                                    FStar_Syntax_Free.names
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2679
                                                                    (FStar_Util.set_mem
                                                                    (Prims.fst
                                                                    type_param1))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____2678
                                                                    Prims.op_Negation)
                                                                    wp_binders1
                                                                     in
                                                                    (match uu____2662
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
                                                                    uu____2710
                                                                    ->
                                                                    let uu____2714
                                                                    =
                                                                    let uu____2715
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: multiple post candidates %s"
                                                                    uu____2715
                                                                     in
                                                                    failwith
                                                                    uu____2714
                                                                     in
                                                                    let uu____2718
                                                                    =
                                                                    FStar_Syntax_Util.arrow
                                                                    pre_args
                                                                    c1  in
                                                                    let uu____2719
                                                                    =
                                                                    FStar_Syntax_Util.abs
                                                                    (type_param1
                                                                    ::
                                                                    effect_param1)
                                                                    (Prims.fst
                                                                    post).FStar_Syntax_Syntax.sort
                                                                    None  in
                                                                    (uu____2718,
                                                                    uu____2719)))
                                                              | uu____2727 ->
                                                                  let uu____2728
                                                                    =
                                                                    let uu____2729
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    arrow2
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Impossible: pre/post arrow %s"
                                                                    uu____2729
                                                                     in
                                                                  failwith
                                                                    uu____2728))
                                                    | uu____2732 ->
                                                        let uu____2733 =
                                                          let uu____2734 =
                                                            FStar_Syntax_Print.term_to_string
                                                              wp_type1
                                                             in
                                                          FStar_Util.format1
                                                            "Impossible: pre/post abs %s"
                                                            uu____2734
                                                           in
                                                        failwith uu____2733
                                                     in
                                                  (match uu____2530 with
                                                   | (pre,post) ->
                                                       ((let uu____2745 =
                                                           register "pre" pre
                                                            in
                                                         ());
                                                        (let uu____2747 =
                                                           register "post"
                                                             post
                                                            in
                                                         ());
                                                        (let uu____2749 =
                                                           register "wp"
                                                             wp_type1
                                                            in
                                                         ());
                                                        (let ed1 =
                                                           let uu___100_2751
                                                             = ed  in
                                                           let uu____2752 =
                                                             FStar_Syntax_Subst.close_binders
                                                               effect_binders1
                                                              in
                                                           let uu____2753 =
                                                             FStar_Syntax_Subst.close
                                                               effect_binders1
                                                               effect_signature1
                                                              in
                                                           let uu____2754 =
                                                             let uu____2755 =
                                                               apply_close
                                                                 return_wp2
                                                                in
                                                             ([], uu____2755)
                                                              in
                                                           let uu____2761 =
                                                             let uu____2762 =
                                                               apply_close
                                                                 bind_wp2
                                                                in
                                                             ([], uu____2762)
                                                              in
                                                           let uu____2768 =
                                                             apply_close
                                                               repr3
                                                              in
                                                           let uu____2769 =
                                                             let uu____2770 =
                                                               apply_close
                                                                 return_elab1
                                                                in
                                                             ([], uu____2770)
                                                              in
                                                           let uu____2776 =
                                                             let uu____2777 =
                                                               apply_close
                                                                 bind_elab1
                                                                in
                                                             ([], uu____2777)
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.qualifiers
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.qualifiers);
                                                             FStar_Syntax_Syntax.cattributes
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.cattributes);
                                                             FStar_Syntax_Syntax.mname
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.univs
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.univs);
                                                             FStar_Syntax_Syntax.binders
                                                               = uu____2752;
                                                             FStar_Syntax_Syntax.signature
                                                               = uu____2753;
                                                             FStar_Syntax_Syntax.ret_wp
                                                               = uu____2754;
                                                             FStar_Syntax_Syntax.bind_wp
                                                               = uu____2761;
                                                             FStar_Syntax_Syntax.if_then_else
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.if_then_else);
                                                             FStar_Syntax_Syntax.ite_wp
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.ite_wp);
                                                             FStar_Syntax_Syntax.stronger
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.stronger);
                                                             FStar_Syntax_Syntax.close_wp
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.close_wp);
                                                             FStar_Syntax_Syntax.assert_p
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.assert_p);
                                                             FStar_Syntax_Syntax.assume_p
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.assume_p);
                                                             FStar_Syntax_Syntax.null_wp
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.null_wp);
                                                             FStar_Syntax_Syntax.trivial
                                                               =
                                                               (uu___100_2751.FStar_Syntax_Syntax.trivial);
                                                             FStar_Syntax_Syntax.repr
                                                               = uu____2768;
                                                             FStar_Syntax_Syntax.return_repr
                                                               = uu____2769;
                                                             FStar_Syntax_Syntax.bind_repr
                                                               = uu____2776;
                                                             FStar_Syntax_Syntax.actions
                                                               = actions1
                                                           }  in
                                                         let uu____2783 =
                                                           FStar_TypeChecker_DMFF.gen_wps_for_free
                                                             env1
                                                             effect_binders1
                                                             a1 wp_a ed1
                                                            in
                                                         match uu____2783
                                                         with
                                                         | (sigelts',ed2) ->
                                                             ((let uu____2794
                                                                 =
                                                                 FStar_TypeChecker_Env.debug
                                                                   env1
                                                                   (FStar_Options.Other
                                                                    "ED")
                                                                  in
                                                               if uu____2794
                                                               then
                                                                 let uu____2795
                                                                   =
                                                                   FStar_Syntax_Print.eff_decl_to_string
                                                                    true ed2
                                                                    in
                                                                 FStar_Util.print_string
                                                                   uu____2795
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
                                                                    let uu____2813
                                                                    =
                                                                    let uu____2815
                                                                    =
                                                                    apply_close
                                                                    lift_from_pure_wp1
                                                                     in
                                                                    Some
                                                                    uu____2815
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
                                                                    uu____2813;
                                                                    FStar_Syntax_Syntax.sub_eff_lift
                                                                    = None
                                                                    }  in
                                                                   Some
                                                                    (FStar_Syntax_Syntax.Sig_sub_effect
                                                                    (lift_from_pure,
                                                                    FStar_Range.dummyRange))
                                                                 else None
                                                                  in
                                                               let uu____2823
                                                                 =
                                                                 let uu____2825
                                                                   =
                                                                   let uu____2827
                                                                    =
                                                                    FStar_ST.read
                                                                    sigelts
                                                                     in
                                                                   FStar_List.rev
                                                                    uu____2827
                                                                    in
                                                                 FStar_List.append
                                                                   uu____2825
                                                                   sigelts'
                                                                  in
                                                               (uu____2823,
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
              (lex_t1,[],[],t,uu____2850,uu____2851,[],r))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_top1,[],_t_top,_lex_t_top,_0_28,[],uu____2856,r1))::(FStar_Syntax_Syntax.Sig_datacon
              (lex_cons,[],_t_cons,_lex_t_cons,_0_29,[],uu____2861,r2))::[]
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
                let uu____2905 =
                  let uu____2908 =
                    let uu____2909 =
                      let uu____2914 =
                        FStar_Syntax_Syntax.fvar
                          (FStar_Ident.set_lid_range
                             FStar_Syntax_Const.lex_t_lid r1)
                          FStar_Syntax_Syntax.Delta_constant None
                         in
                      (uu____2914, [FStar_Syntax_Syntax.U_name utop])  in
                    FStar_Syntax_Syntax.Tm_uinst uu____2909  in
                  FStar_Syntax_Syntax.mk uu____2908  in
                uu____2905 None r1  in
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
                  let uu____2933 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_type
                         (FStar_Syntax_Syntax.U_name ucons1)) None r2
                     in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2933  in
                let hd1 =
                  let uu____2939 = FStar_Syntax_Syntax.bv_to_name a  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2939  in
                let tl1 =
                  let uu____2941 =
                    let uu____2942 =
                      let uu____2945 =
                        let uu____2946 =
                          let uu____2951 =
                            FStar_Syntax_Syntax.fvar
                              (FStar_Ident.set_lid_range
                                 FStar_Syntax_Const.lex_t_lid r2)
                              FStar_Syntax_Syntax.Delta_constant None
                             in
                          (uu____2951, [FStar_Syntax_Syntax.U_name ucons2])
                           in
                        FStar_Syntax_Syntax.Tm_uinst uu____2946  in
                      FStar_Syntax_Syntax.mk uu____2945  in
                    uu____2942 None r2  in
                  FStar_Syntax_Syntax.new_bv (Some r2) uu____2941  in
                let res =
                  let uu____2964 =
                    let uu____2967 =
                      let uu____2968 =
                        let uu____2973 =
                          FStar_Syntax_Syntax.fvar
                            (FStar_Ident.set_lid_range
                               FStar_Syntax_Const.lex_t_lid r2)
                            FStar_Syntax_Syntax.Delta_constant None
                           in
                        (uu____2973,
                          [FStar_Syntax_Syntax.U_max
                             [FStar_Syntax_Syntax.U_name ucons1;
                             FStar_Syntax_Syntax.U_name ucons2]])
                         in
                      FStar_Syntax_Syntax.Tm_uinst uu____2968  in
                    FStar_Syntax_Syntax.mk uu____2967  in
                  uu____2964 None r2  in
                let uu____2983 = FStar_Syntax_Syntax.mk_Total res  in
                FStar_Syntax_Util.arrow
                  [(a, (Some FStar_Syntax_Syntax.imp_tag));
                  (hd1, None);
                  (tl1, None)] uu____2983
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
              let uu____3004 =
                let uu____3012 = FStar_TypeChecker_Env.get_range env  in
                ([tc; dc_lextop; dc_lexcons], [], lids, uu____3012)  in
              FStar_Syntax_Syntax.Sig_bundle uu____3004
          | uu____3016 ->
              let uu____3018 =
                let uu____3019 =
                  FStar_Syntax_Print.sigelt_to_string
                    (FStar_Syntax_Syntax.Sig_bundle
                       (ses, [], lids, FStar_Range.dummyRange))
                   in
                FStar_Util.format1 "Unexpected lex_t: %s\n" uu____3019  in
              failwith uu____3018

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
            let uu____3030 = FStar_Syntax_Util.type_u ()  in
            match uu____3030 with
            | (k,uu____3034) ->
                let phi1 =
                  let uu____3036 = tc_check_trivial_guard env1 phi k  in
                  FStar_All.pipe_right uu____3036
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
          let uu____3047 =
            FStar_TypeChecker_TcInductive.check_inductive_well_typedness env
              ses quals lids
             in
          match uu____3047 with
          | (sig_bndle,tcs,datas) ->
              let data_ops_ses =
                let uu____3066 =
                  FStar_List.map
                    (FStar_TypeChecker_Util.mk_data_operations quals env tcs)
                    datas
                   in
                FStar_All.pipe_right uu____3066 FStar_List.flatten  in
              ((let uu____3074 =
                  (FStar_Options.no_positivity ()) || (FStar_Options.lax ())
                   in
                if uu____3074
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
                          let uu____3080 =
                            match ty with
                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                (lid,uu____3086,uu____3087,uu____3088,uu____3089,uu____3090,uu____3091,r)
                                -> (lid, r)
                            | uu____3099 -> failwith "Impossible!"  in
                          match uu____3080 with
                          | (lid,r) ->
                              FStar_Errors.report r
                                (Prims.strcat "Inductive type "
                                   (Prims.strcat lid.FStar_Ident.str
                                      " does not satisfy the positivity condition"))
                        else ()) tcs));
               (let skip_prims_type uu____3108 =
                  let lid =
                    let ty = FStar_List.hd tcs  in
                    match ty with
                    | FStar_Syntax_Syntax.Sig_inductive_typ
                        (lid,uu____3112,uu____3113,uu____3114,uu____3115,uu____3116,uu____3117,uu____3118)
                        -> lid
                    | uu____3125 -> failwith "Impossible"  in
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
                let uu____3131 =
                  (((FStar_List.length tcs) = (Prims.parse_int "0")) ||
                     ((FStar_Ident.lid_equals
                         env.FStar_TypeChecker_Env.curmodule
                         FStar_Syntax_Const.prims_lid)
                        && (skip_prims_type ())))
                    || is_noeq
                   in
                if uu____3131
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
                   let uu____3147 =
                     let uu____3149 =
                       let uu____3150 =
                         let uu____3158 =
                           FStar_TypeChecker_Env.get_range env0  in
                         ((FStar_List.append tcs datas), quals, lids,
                           uu____3158)
                          in
                       FStar_Syntax_Syntax.Sig_bundle uu____3150  in
                     uu____3149 :: ses1  in
                   (uu____3147, data_ops_ses))))

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
           let uu____3198 = FStar_TypeChecker_Env.push_sigelt env2 se1  in
           ([se1], uu____3198, [])
       | FStar_Syntax_Syntax.Sig_bundle (ses,quals,lids,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3212 = tc_inductive env2 ses quals lids  in
           (match uu____3212 with
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
             let uu____3242 = FStar_Options.set_options t s  in
             match uu____3242 with
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
                ((let uu____3260 =
                    FStar_Options.restore_cmd_line_options false  in
                  FStar_All.pipe_right uu____3260 Prims.ignore);
                 (match sopt with
                  | None  -> ()
                  | Some s -> set_options1 FStar_Options.Reset s);
                 (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh
                   ();
                 ([se], env1, [])))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free (ne,r) ->
           let uu____3268 = cps_and_elaborate env1 ne  in
           (match uu____3268 with
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
           let uu____3297 =
             FStar_All.pipe_right ne1.FStar_Syntax_Syntax.actions
               (FStar_List.fold_left
                  (fun uu____3308  ->
                     fun a  ->
                       match uu____3308 with
                       | (env3,ses) ->
                           let se_let =
                             FStar_Syntax_Util.action_as_lb
                               ne1.FStar_Syntax_Syntax.mname a
                              in
                           let uu____3321 =
                             FStar_TypeChecker_Env.push_sigelt env3 se_let
                              in
                           (uu____3321, (se_let :: ses))) (env2, [se1]))
              in
           (match uu____3297 with
            | (env3,ses) ->
                let env4 = FStar_TypeChecker_Util.build_lattice env3 se1  in
                ([se1], env4, []))
       | FStar_Syntax_Syntax.Sig_sub_effect (sub1,r) ->
           let sub2 = tc_subeff_decl env1 sub1 r  in
           let se1 = FStar_Syntax_Syntax.Sig_sub_effect (sub2, r)  in
           let env2 = FStar_TypeChecker_Env.push_sigelt env1 se1  in
           let env3 = FStar_TypeChecker_Util.build_lattice env2 se1  in
           ([se1], env3, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uvs,tps,c,tags,flags,r)
           ->
           let env0 = env1  in
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3358 = FStar_Syntax_Subst.open_comp tps c  in
           (match uu____3358 with
            | (tps1,c1) ->
                let uu____3368 =
                  FStar_TypeChecker_TcTerm.tc_tparams env2 tps1  in
                (match uu____3368 with
                 | (tps2,env3,us) ->
                     let uu____3380 =
                       FStar_TypeChecker_TcTerm.tc_comp env3 c1  in
                     (match uu____3380 with
                      | (c2,u,g) ->
                          (FStar_TypeChecker_Rel.force_trivial_guard env3 g;
                           (let tps3 = FStar_Syntax_Subst.close_binders tps2
                               in
                            let c3 = FStar_Syntax_Subst.close_comp tps3 c2
                               in
                            let uu____3395 =
                              let uu____3396 =
                                FStar_Syntax_Syntax.mk
                                  (FStar_Syntax_Syntax.Tm_arrow (tps3, c3))
                                  None r
                                 in
                              FStar_TypeChecker_Util.generalize_universes
                                env0 uu____3396
                               in
                            match uu____3395 with
                            | (uvs1,t) ->
                                let uu____3410 =
                                  let uu____3418 =
                                    let uu____3421 =
                                      let uu____3422 =
                                        FStar_Syntax_Subst.compress t  in
                                      uu____3422.FStar_Syntax_Syntax.n  in
                                    (tps3, uu____3421)  in
                                  match uu____3418 with
                                  | ([],FStar_Syntax_Syntax.Tm_arrow
                                     (uu____3432,c4)) -> ([], c4)
                                  | (uu____3456,FStar_Syntax_Syntax.Tm_arrow
                                     (tps4,c4)) -> (tps4, c4)
                                  | uu____3474 -> failwith "Impossible"  in
                                (match uu____3410 with
                                 | (tps4,c4) ->
                                     (if
                                        ((FStar_List.length uvs1) <>
                                           (Prims.parse_int "1"))
                                          &&
                                          (Prims.op_Negation
                                             (FStar_Ident.lid_equals lid
                                                FStar_Syntax_Const.effect_Lemma_lid))
                                      then
                                        (let uu____3504 =
                                           FStar_Syntax_Subst.open_univ_vars
                                             uvs1 t
                                            in
                                         match uu____3504 with
                                         | (uu____3507,t1) ->
                                             let uu____3509 =
                                               let uu____3510 =
                                                 let uu____3513 =
                                                   let uu____3514 =
                                                     FStar_Syntax_Print.lid_to_string
                                                       lid
                                                      in
                                                   let uu____3515 =
                                                     FStar_All.pipe_right
                                                       (FStar_List.length
                                                          uvs1)
                                                       FStar_Util.string_of_int
                                                      in
                                                   let uu____3518 =
                                                     FStar_Syntax_Print.term_to_string
                                                       t1
                                                      in
                                                   FStar_Util.format3
                                                     "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                     uu____3514 uu____3515
                                                     uu____3518
                                                    in
                                                 (uu____3513, r)  in
                                               FStar_Errors.Error uu____3510
                                                in
                                             Prims.raise uu____3509)
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
                (fun uu___78_3548  ->
                   match uu___78_3548 with
                   | FStar_Syntax_Syntax.OnlyName  -> true
                   | uu____3549 -> false))
           -> ([], env1, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uvs,t,quals,r) ->
           let env2 = FStar_TypeChecker_Env.set_range env1 r  in
           let uu____3560 =
             if uvs = []
             then
               let uu____3561 =
                 let uu____3562 = FStar_Syntax_Util.type_u ()  in
                 Prims.fst uu____3562  in
               check_and_gen env2 t uu____3561
             else
               (let uu____3566 = FStar_Syntax_Subst.open_univ_vars uvs t  in
                match uu____3566 with
                | (uvs1,t1) ->
                    let t2 =
                      let uu____3572 =
                        let uu____3573 = FStar_Syntax_Util.type_u ()  in
                        Prims.fst uu____3573  in
                      tc_check_trivial_guard env2 t1 uu____3572  in
                    let t3 =
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Normalize.NoFullNorm;
                        FStar_TypeChecker_Normalize.Beta] env2 t2
                       in
                    let uu____3577 =
                      FStar_Syntax_Subst.close_univ_vars uvs1 t3  in
                    (uvs1, uu____3577))
              in
           (match uu____3560 with
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
           let uu____3607 = FStar_TypeChecker_TcTerm.tc_term env3 e  in
           (match uu____3607 with
            | (e1,c,g1) ->
                let uu____3619 =
                  let uu____3623 =
                    let uu____3625 =
                      FStar_Syntax_Util.ml_comp
                        FStar_TypeChecker_Common.t_unit r
                       in
                    Some uu____3625  in
                  let uu____3626 =
                    let uu____3629 = c.FStar_Syntax_Syntax.lcomp_as_comp ()
                       in
                    (e1, uu____3629)  in
                  FStar_TypeChecker_TcTerm.check_expected_effect env3
                    uu____3623 uu____3626
                   in
                (match uu____3619 with
                 | (e2,uu____3640,g) ->
                     ((let uu____3643 = FStar_TypeChecker_Rel.conj_guard g1 g
                          in
                       FStar_TypeChecker_Rel.force_trivial_guard env3
                         uu____3643);
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
                 let uu____3685 =
                   ((FStar_List.length q) = (FStar_List.length q')) &&
                     (FStar_List.forall2 FStar_Syntax_Util.qualifier_equal q
                        q')
                    in
                 if uu____3685
                 then Some q
                 else
                   (let uu____3694 =
                      let uu____3695 =
                        let uu____3698 =
                          let uu____3699 = FStar_Syntax_Print.lid_to_string l
                             in
                          let uu____3700 =
                            FStar_Syntax_Print.quals_to_string q  in
                          let uu____3701 =
                            FStar_Syntax_Print.quals_to_string q'  in
                          FStar_Util.format3
                            "Inconsistent qualifier annotations on %s; Expected {%s}, got {%s}"
                            uu____3699 uu____3700 uu____3701
                           in
                        (uu____3698, r)  in
                      FStar_Errors.Error uu____3695  in
                    Prims.raise uu____3694)
              in
           let uu____3704 =
             FStar_All.pipe_right (Prims.snd lbs)
               (FStar_List.fold_left
                  (fun uu____3725  ->
                     fun lb  ->
                       match uu____3725 with
                       | (gen1,lbs1,quals_opt) ->
                           let lbname =
                             FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                              in
                           let uu____3749 =
                             let uu____3755 =
                               FStar_TypeChecker_Env.try_lookup_val_decl env2
                                 (lbname.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                in
                             match uu____3755 with
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
                                   | uu____3807 ->
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
                                  (let uu____3815 =
                                     FStar_Syntax_Syntax.mk_lb
                                       ((FStar_Util.Inr lbname), uvs,
                                         FStar_Syntax_Const.effect_ALL_lid,
                                         tval,
                                         (lb.FStar_Syntax_Syntax.lbdef))
                                      in
                                   (false, uu____3815, quals_opt1)))
                              in
                           (match uu____3749 with
                            | (gen2,lb1,quals_opt1) ->
                                (gen2, (lb1 :: lbs1), quals_opt1)))
                  (true, [], (if quals = [] then None else Some quals)))
              in
           (match uu____3704 with
            | (should_generalize,lbs',quals_opt) ->
                let quals1 =
                  match quals_opt with
                  | None  -> [FStar_Syntax_Syntax.Visible_default]
                  | Some q ->
                      let uu____3869 =
                        FStar_All.pipe_right q
                          (FStar_Util.for_some
                             (fun uu___79_3871  ->
                                match uu___79_3871 with
                                | FStar_Syntax_Syntax.Irreducible 
                                  |FStar_Syntax_Syntax.Visible_default 
                                   |FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
                                    -> true
                                | uu____3872 -> false))
                         in
                      if uu____3869
                      then q
                      else FStar_Syntax_Syntax.Visible_default :: q
                   in
                let lbs'1 = FStar_List.rev lbs'  in
                let e =
                  let uu____3880 =
                    let uu____3883 =
                      let uu____3884 =
                        let uu____3892 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_constant
                               FStar_Const.Const_unit) None r
                           in
                        (((Prims.fst lbs), lbs'1), uu____3892)  in
                      FStar_Syntax_Syntax.Tm_let uu____3884  in
                    FStar_Syntax_Syntax.mk uu____3883  in
                  uu____3880 None r  in
                let uu____3914 =
                  let uu____3920 =
                    FStar_TypeChecker_TcTerm.tc_maybe_toplevel_term
                      (let uu___101_3924 = env2  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___101_3924.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___101_3924.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___101_3924.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___101_3924.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___101_3924.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___101_3924.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___101_3924.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___101_3924.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___101_3924.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___101_3924.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___101_3924.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize = should_generalize;
                         FStar_TypeChecker_Env.letrecs =
                           (uu___101_3924.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = true;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___101_3924.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___101_3924.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___101_3924.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___101_3924.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (uu___101_3924.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___101_3924.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.type_of =
                           (uu___101_3924.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___101_3924.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___101_3924.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qname_and_index =
                           (uu___101_3924.FStar_TypeChecker_Env.qname_and_index)
                       }) e
                     in
                  match uu____3920 with
                  | ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_let
                         (lbs1,e1);
                       FStar_Syntax_Syntax.tk = uu____3932;
                       FStar_Syntax_Syntax.pos = uu____3933;
                       FStar_Syntax_Syntax.vars = uu____3934;_},uu____3935,g)
                      when FStar_TypeChecker_Rel.is_trivial g ->
                      let quals2 =
                        match e1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_meta
                            (uu____3954,FStar_Syntax_Syntax.Meta_desugared
                             (FStar_Syntax_Syntax.Masked_effect ))
                            -> FStar_Syntax_Syntax.HasMaskedEffect :: quals1
                        | uu____3959 -> quals1  in
                      ((FStar_Syntax_Syntax.Sig_let
                          (lbs1, r, lids, quals2, attrs)), lbs1)
                  | uu____3969 -> failwith "impossible"  in
                (match uu____3914 with
                 | (se1,lbs1) ->
                     ((let uu____3992 = log env2  in
                       if uu____3992
                       then
                         let uu____3993 =
                           let uu____3994 =
                             FStar_All.pipe_right (Prims.snd lbs1)
                               (FStar_List.map
                                  (fun lb  ->
                                     let should_log =
                                       let uu____4001 =
                                         let uu____4006 =
                                           let uu____4007 =
                                             let uu____4012 =
                                               FStar_Util.right
                                                 lb.FStar_Syntax_Syntax.lbname
                                                in
                                             uu____4012.FStar_Syntax_Syntax.fv_name
                                              in
                                           uu____4007.FStar_Syntax_Syntax.v
                                            in
                                         FStar_TypeChecker_Env.try_lookup_val_decl
                                           env2 uu____4006
                                          in
                                       match uu____4001 with
                                       | None  -> true
                                       | uu____4019 -> false  in
                                     if should_log
                                     then
                                       let uu____4024 =
                                         FStar_Syntax_Print.lbname_to_string
                                           lb.FStar_Syntax_Syntax.lbname
                                          in
                                       let uu____4025 =
                                         FStar_Syntax_Print.term_to_string
                                           lb.FStar_Syntax_Syntax.lbtyp
                                          in
                                       FStar_Util.format2 "let %s : %s"
                                         uu____4024 uu____4025
                                     else ""))
                              in
                           FStar_All.pipe_right uu____3994
                             (FStar_String.concat "\n")
                            in
                         FStar_Util.print1 "%s\n" uu____3993
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
             (fun uu___80_4055  ->
                match uu___80_4055 with
                | FStar_Syntax_Syntax.Abstract  -> true
                | uu____4056 -> false))
         in
      let is_hidden_proj_or_disc q =
        match q with
        | FStar_Syntax_Syntax.Projector (l,_)
          |FStar_Syntax_Syntax.Discriminator l ->
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Ident.lid_equals l))
        | uu____4064 -> false  in
      match se with
      | FStar_Syntax_Syntax.Sig_pragma uu____4069 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_inductive_typ _
        |FStar_Syntax_Syntax.Sig_datacon _ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4082,r) ->
          let uu____4090 = is_abstract quals  in
          if uu____4090
          then
            let for_export_bundle se1 uu____4109 =
              match uu____4109 with
              | (out,hidden1) ->
                  (match se1 with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,us,bs,t,uu____4132,uu____4133,quals1,r1) ->
                       let dec =
                         let uu____4143 =
                           let uu____4150 =
                             FStar_Syntax_Util.maybe_tot_arrow bs t  in
                           (l, us, uu____4150,
                             (FStar_Syntax_Syntax.Assumption ::
                             FStar_Syntax_Syntax.New :: quals1), r1)
                            in
                         FStar_Syntax_Syntax.Sig_declare_typ uu____4143  in
                       ((dec :: out), hidden1)
                   | FStar_Syntax_Syntax.Sig_datacon
                       (l,us,t,uu____4157,uu____4158,uu____4159,uu____4160,r1)
                       ->
                       let dec =
                         FStar_Syntax_Syntax.Sig_declare_typ
                           (l, us, t, [FStar_Syntax_Syntax.Assumption], r1)
                          in
                       ((dec :: out), (l :: hidden1))
                   | uu____4170 -> (out, hidden1))
               in
            FStar_List.fold_right for_export_bundle ses ([], hidden)
          else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_assume
          (uu____4182,uu____4183,quals,uu____4185) ->
          let uu____4188 = is_abstract quals  in
          if uu____4188 then ([], hidden) else ([se], hidden)
      | FStar_Syntax_Syntax.Sig_declare_typ (l,us,t,quals,r) ->
          let uu____4205 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some is_hidden_proj_or_disc)
             in
          if uu____4205
          then
            ([FStar_Syntax_Syntax.Sig_declare_typ
                (l, us, t, [FStar_Syntax_Syntax.Assumption], r)], (l ::
              hidden))
          else
            (let uu____4215 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___81_4217  ->
                       match uu___81_4217 with
                       | FStar_Syntax_Syntax.Assumption 
                         |FStar_Syntax_Syntax.Projector _
                          |FStar_Syntax_Syntax.Discriminator _ -> true
                       | uu____4220 -> false))
                in
             if uu____4215 then ([se], hidden) else ([], hidden))
      | FStar_Syntax_Syntax.Sig_main uu____4230 -> ([], hidden)
      | FStar_Syntax_Syntax.Sig_new_effect _
        |FStar_Syntax_Syntax.Sig_new_effect_for_free _
         |FStar_Syntax_Syntax.Sig_sub_effect _
          |FStar_Syntax_Syntax.Sig_effect_abbrev _ -> ([se], hidden)
      | FStar_Syntax_Syntax.Sig_let
          ((false ,lb::[]),uu____4242,uu____4243,quals,uu____4245) when
          FStar_All.pipe_right quals
            (FStar_Util.for_some is_hidden_proj_or_disc)
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          let uu____4263 =
            FStar_All.pipe_right hidden
              (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq_lid fv))
             in
          if uu____4263
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
      | FStar_Syntax_Syntax.Sig_let (lbs,r,l,quals,uu____4287) ->
          let uu____4294 = is_abstract quals  in
          if uu____4294
          then
            let uu____4299 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu____4305 =
                        let uu____4312 =
                          let uu____4313 =
                            let uu____4318 =
                              FStar_Util.right lb.FStar_Syntax_Syntax.lbname
                               in
                            uu____4318.FStar_Syntax_Syntax.fv_name  in
                          uu____4313.FStar_Syntax_Syntax.v  in
                        (uu____4312, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp),
                          (FStar_Syntax_Syntax.Assumption :: quals), r)
                         in
                      FStar_Syntax_Syntax.Sig_declare_typ uu____4305))
               in
            (uu____4299, hidden)
          else ([se], hidden)
  
let tc_decls :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.sigelt
        Prims.list * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun ses  ->
      let rec process_one_decl uu____4366 se =
        match uu____4366 with
        | (ses1,exports,env1,hidden) ->
            ((let uu____4396 =
                FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
              if uu____4396
              then
                let uu____4397 = FStar_Syntax_Print.sigelt_to_string se  in
                FStar_Util.print1
                  ">>>>>>>>>>>>>>Checking top-level decl %s\n" uu____4397
              else ());
             (let uu____4399 = tc_decl env1 se  in
              match uu____4399 with
              | (ses',env2,ses_elaborated) ->
                  ((let uu____4423 =
                      (FStar_Options.log_types ()) ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "LogTypes"))
                       in
                    if uu____4423
                    then
                      let uu____4424 =
                        FStar_List.fold_left
                          (fun s  ->
                             fun se1  ->
                               let uu____4427 =
                                 let uu____4428 =
                                   FStar_Syntax_Print.sigelt_to_string se1
                                    in
                                 Prims.strcat uu____4428 "\n"  in
                               Prims.strcat s uu____4427) "" ses'
                         in
                      FStar_Util.print1 "Checked: %s\n" uu____4424
                    else ());
                   FStar_List.iter
                     (fun se1  ->
                        (env2.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_sig
                          env2 se1) ses';
                   (let uu____4432 =
                      let accum_exports_hidden uu____4450 se1 =
                        match uu____4450 with
                        | (exports1,hidden1) ->
                            let uu____4466 = for_export hidden1 se1  in
                            (match uu____4466 with
                             | (se_exported,hidden2) ->
                                 ((FStar_List.rev_append se_exported exports1),
                                   hidden2))
                         in
                      FStar_List.fold_left accum_exports_hidden
                        (exports, hidden) ses'
                       in
                    match uu____4432 with
                    | (exports1,hidden1) ->
                        (((FStar_List.rev_append ses' ses1), exports1, env2,
                           hidden1), ses_elaborated)))))
         in
      let uu____4516 =
        FStar_Util.fold_flatten process_one_decl ([], [], env, []) ses  in
      match uu____4516 with
      | (ses1,exports,env1,uu____4542) ->
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
      (let uu____4567 = FStar_Options.debug_any ()  in
       if uu____4567
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
         let uu___102_4573 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___102_4573.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___102_4573.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___102_4573.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___102_4573.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___102_4573.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___102_4573.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___102_4573.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___102_4573.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___102_4573.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___102_4573.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___102_4573.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___102_4573.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___102_4573.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___102_4573.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___102_4573.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___102_4573.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (modul.FStar_Syntax_Syntax.is_interface);
           FStar_TypeChecker_Env.admit = (Prims.op_Negation verify);
           FStar_TypeChecker_Env.lax =
             (uu___102_4573.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___102_4573.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___102_4573.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___102_4573.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___102_4573.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___102_4573.FStar_TypeChecker_Env.qname_and_index)
         }  in
       (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.push msg;
       (let env2 =
          FStar_TypeChecker_Env.set_current_module env1
            modul.FStar_Syntax_Syntax.name
           in
        let uu____4576 = tc_decls env2 modul.FStar_Syntax_Syntax.declarations
           in
        match uu____4576 with
        | (ses,exports,env3) ->
            ((let uu___103_4594 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___103_4594.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations = ses;
                FStar_Syntax_Syntax.exports =
                  (uu___103_4594.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___103_4594.FStar_Syntax_Syntax.is_interface)
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
        let uu____4610 = tc_decls env decls  in
        match uu____4610 with
        | (ses,exports,env1) ->
            let modul1 =
              let uu___104_4628 = modul  in
              {
                FStar_Syntax_Syntax.name =
                  (uu___104_4628.FStar_Syntax_Syntax.name);
                FStar_Syntax_Syntax.declarations =
                  (FStar_List.append modul.FStar_Syntax_Syntax.declarations
                     ses);
                FStar_Syntax_Syntax.exports =
                  (uu___104_4628.FStar_Syntax_Syntax.exports);
                FStar_Syntax_Syntax.is_interface =
                  (uu___104_4628.FStar_Syntax_Syntax.is_interface)
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
          let uu___105_4642 = env  in
          {
            FStar_TypeChecker_Env.solver =
              (uu___105_4642.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range =
              (uu___105_4642.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (uu___105_4642.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma =
              (uu___105_4642.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_cache =
              (uu___105_4642.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (uu___105_4642.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (uu___105_4642.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab =
              (uu___105_4642.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.is_pattern =
              (uu___105_4642.FStar_TypeChecker_Env.is_pattern);
            FStar_TypeChecker_Env.instantiate_imp =
              (uu___105_4642.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (uu___105_4642.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (uu___105_4642.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (uu___105_4642.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level = true;
            FStar_TypeChecker_Env.check_uvars =
              (uu___105_4642.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq =
              (uu___105_4642.FStar_TypeChecker_Env.use_eq);
            FStar_TypeChecker_Env.is_iface =
              (uu___105_4642.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit =
              (uu___105_4642.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = true;
            FStar_TypeChecker_Env.lax_universes = true;
            FStar_TypeChecker_Env.type_of =
              (uu___105_4642.FStar_TypeChecker_Env.type_of);
            FStar_TypeChecker_Env.universe_of =
              (uu___105_4642.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.use_bv_sorts =
              (uu___105_4642.FStar_TypeChecker_Env.use_bv_sorts);
            FStar_TypeChecker_Env.qname_and_index =
              (uu___105_4642.FStar_TypeChecker_Env.qname_and_index)
          }  in
        let check_term lid univs1 t =
          let uu____4653 = FStar_Syntax_Subst.open_univ_vars univs1 t  in
          match uu____4653 with
          | (univs2,t1) ->
              ((let uu____4659 =
                  let uu____4660 =
                    let uu____4663 =
                      FStar_TypeChecker_Env.set_current_module env1
                        modul.FStar_Syntax_Syntax.name
                       in
                    FStar_TypeChecker_Env.debug uu____4663  in
                  FStar_All.pipe_left uu____4660
                    (FStar_Options.Other "Exports")
                   in
                if uu____4659
                then
                  let uu____4664 = FStar_Syntax_Print.lid_to_string lid  in
                  let uu____4665 =
                    let uu____4666 =
                      FStar_All.pipe_right univs2
                        (FStar_List.map
                           (fun x  ->
                              FStar_Syntax_Print.univ_to_string
                                (FStar_Syntax_Syntax.U_name x)))
                       in
                    FStar_All.pipe_right uu____4666
                      (FStar_String.concat ", ")
                     in
                  let uu____4671 = FStar_Syntax_Print.term_to_string t1  in
                  FStar_Util.print3 "Checking for export %s <%s> : %s\n"
                    uu____4664 uu____4665 uu____4671
                else ());
               (let env2 = FStar_TypeChecker_Env.push_univ_vars env1 univs2
                   in
                let uu____4674 =
                  FStar_TypeChecker_TcTerm.tc_trivial_guard env2 t1  in
                FStar_All.pipe_right uu____4674 Prims.ignore))
           in
        let check_term1 lid univs1 t =
          (let uu____4692 =
             let uu____4693 =
               FStar_Syntax_Print.lid_to_string
                 modul.FStar_Syntax_Syntax.name
                in
             let uu____4694 = FStar_Syntax_Print.lid_to_string lid  in
             FStar_Util.format2
               "Interface of %s violates its abstraction (add a 'private' qualifier to '%s'?)"
               uu____4693 uu____4694
              in
           FStar_Errors.message_prefix.FStar_Errors.set_prefix uu____4692);
          check_term lid univs1 t;
          FStar_Errors.message_prefix.FStar_Errors.clear_prefix ()  in
        let rec check_sigelt uu___82_4699 =
          match uu___82_4699 with
          | FStar_Syntax_Syntax.Sig_bundle (ses,quals,uu____4702,uu____4703)
              ->
              let uu____4710 =
                let uu____4711 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4711  in
              if uu____4710
              then FStar_All.pipe_right ses (FStar_List.iter check_sigelt)
              else ()
          | FStar_Syntax_Syntax.Sig_inductive_typ
              (l,univs1,binders,typ,uu____4719,uu____4720,uu____4721,r) ->
              let t =
                let uu____4732 =
                  let uu____4735 =
                    let uu____4736 =
                      let uu____4744 = FStar_Syntax_Syntax.mk_Total typ  in
                      (binders, uu____4744)  in
                    FStar_Syntax_Syntax.Tm_arrow uu____4736  in
                  FStar_Syntax_Syntax.mk uu____4735  in
                uu____4732 None r  in
              check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_datacon
              (l,univs1,t,uu____4756,uu____4757,uu____4758,uu____4759,uu____4760)
              -> check_term1 l univs1 t
          | FStar_Syntax_Syntax.Sig_declare_typ (l,univs1,t,quals,uu____4769)
              ->
              let uu____4772 =
                let uu____4773 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4773  in
              if uu____4772 then check_term1 l univs1 t else ()
          | FStar_Syntax_Syntax.Sig_let
              ((uu____4776,lbs),uu____4778,uu____4779,quals,uu____4781) ->
              let uu____4793 =
                let uu____4794 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4794  in
              if uu____4793
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
              let uu____4815 =
                let uu____4816 =
                  FStar_All.pipe_right quals
                    (FStar_List.contains FStar_Syntax_Syntax.Private)
                   in
                Prims.op_Negation uu____4816  in
              if uu____4815
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
          let uu___106_4849 = modul  in
          {
            FStar_Syntax_Syntax.name =
              (uu___106_4849.FStar_Syntax_Syntax.name);
            FStar_Syntax_Syntax.declarations =
              (uu___106_4849.FStar_Syntax_Syntax.declarations);
            FStar_Syntax_Syntax.exports = exports;
            FStar_Syntax_Syntax.is_interface =
              (modul.FStar_Syntax_Syntax.is_interface)
          }  in
        let env1 = FStar_TypeChecker_Env.finish_module env modul1  in
        (let uu____4852 =
           let uu____4853 = FStar_Options.lax ()  in
           Prims.op_Negation uu____4853  in
         if uu____4852 then check_exports env1 modul1 exports else ());
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.pop
          (Prims.strcat "Ending modul "
             (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str);
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.encode_modul
          env1 modul1;
        (env1.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.refresh ();
        (let uu____4859 =
           let uu____4860 = FStar_Options.interactive ()  in
           Prims.op_Negation uu____4860  in
         if uu____4859
         then
           let uu____4861 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_right uu____4861 Prims.ignore
         else ());
        (modul1, env1)
  
let tc_modul :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun modul  ->
      let uu____4871 = tc_partial_modul env modul  in
      match uu____4871 with
      | (modul1,non_private_decls,env1) ->
          finish_partial_modul env1 modul1 non_private_decls
  
let check_module :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Syntax_Syntax.modul * FStar_TypeChecker_Env.env)
  =
  fun env  ->
    fun m  ->
      (let uu____4892 = FStar_Options.debug_any ()  in
       if uu____4892
       then
         let uu____4893 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name  in
         FStar_Util.print2 "Checking %s: %s\n"
           (if m.FStar_Syntax_Syntax.is_interface then "i'face" else "module")
           uu____4893
       else ());
      (let env1 =
         let uu___107_4897 = env  in
         let uu____4898 =
           let uu____4899 =
             FStar_Options.should_verify
               (m.FStar_Syntax_Syntax.name).FStar_Ident.str
              in
           Prims.op_Negation uu____4899  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___107_4897.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___107_4897.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___107_4897.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___107_4897.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___107_4897.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___107_4897.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___107_4897.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___107_4897.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___107_4897.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___107_4897.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___107_4897.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___107_4897.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs =
             (uu___107_4897.FStar_TypeChecker_Env.letrecs);
           FStar_TypeChecker_Env.top_level =
             (uu___107_4897.FStar_TypeChecker_Env.top_level);
           FStar_TypeChecker_Env.check_uvars =
             (uu___107_4897.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___107_4897.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___107_4897.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___107_4897.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax = uu____4898;
           FStar_TypeChecker_Env.lax_universes =
             (uu___107_4897.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.type_of =
             (uu___107_4897.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___107_4897.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___107_4897.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qname_and_index =
             (uu___107_4897.FStar_TypeChecker_Env.qname_and_index)
         }  in
       let uu____4900 = tc_modul env1 m  in
       match uu____4900 with
       | (m1,env2) ->
           ((let uu____4908 =
               FStar_Options.dump_module
                 (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                in
             if uu____4908
             then
               let uu____4909 = FStar_Syntax_Print.modul_to_string m1  in
               FStar_Util.print1 "%s\n" uu____4909
             else ());
            (let uu____4912 =
               (FStar_Options.dump_module
                  (m1.FStar_Syntax_Syntax.name).FStar_Ident.str)
                 &&
                 (FStar_Options.debug_at_level
                    (m1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    (FStar_Options.Other "Normalize"))
                in
             if uu____4912
             then
               let normalize_toplevel_lets uu___83_4916 =
                 match uu___83_4916 with
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
                       let uu____4943 =
                         FStar_Syntax_Subst.open_univ_vars
                           lb.FStar_Syntax_Syntax.lbunivs
                           lb.FStar_Syntax_Syntax.lbdef
                          in
                       match uu____4943 with
                       | (univnames1,e) ->
                           let uu___108_4948 = lb  in
                           let uu____4949 =
                             let uu____4952 =
                               FStar_TypeChecker_Env.push_univ_vars env2
                                 univnames1
                                in
                             n1 uu____4952 e  in
                           {
                             FStar_Syntax_Syntax.lbname =
                               (uu___108_4948.FStar_Syntax_Syntax.lbname);
                             FStar_Syntax_Syntax.lbunivs =
                               (uu___108_4948.FStar_Syntax_Syntax.lbunivs);
                             FStar_Syntax_Syntax.lbtyp =
                               (uu___108_4948.FStar_Syntax_Syntax.lbtyp);
                             FStar_Syntax_Syntax.lbeff =
                               (uu___108_4948.FStar_Syntax_Syntax.lbeff);
                             FStar_Syntax_Syntax.lbdef = uu____4949
                           }
                        in
                     let uu____4953 =
                       let uu____4962 =
                         let uu____4966 = FStar_List.map update lbs  in
                         (b, uu____4966)  in
                       (uu____4962, r, ids, qs, attrs)  in
                     FStar_Syntax_Syntax.Sig_let uu____4953
                 | se -> se  in
               let normalized_module =
                 let uu___109_4977 = m1  in
                 let uu____4978 =
                   FStar_List.map normalize_toplevel_lets
                     m1.FStar_Syntax_Syntax.declarations
                    in
                 {
                   FStar_Syntax_Syntax.name =
                     (uu___109_4977.FStar_Syntax_Syntax.name);
                   FStar_Syntax_Syntax.declarations = uu____4978;
                   FStar_Syntax_Syntax.exports =
                     (uu___109_4977.FStar_Syntax_Syntax.exports);
                   FStar_Syntax_Syntax.is_interface =
                     (uu___109_4977.FStar_Syntax_Syntax.is_interface)
                 }  in
               let uu____4979 =
                 FStar_Syntax_Print.modul_to_string normalized_module  in
               FStar_Util.print1 "%s\n" uu____4979
             else ());
            (m1, env2)))
  