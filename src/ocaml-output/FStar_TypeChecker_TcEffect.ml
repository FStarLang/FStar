open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env  -> fun ed  -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed 
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env  ->
    fun eff_name  ->
      fun comb  ->
        fun n  ->
          fun uu____58  ->
            match uu____58 with
            | (us,t) ->
                let uu____80 = FStar_Syntax_Subst.open_univ_vars us t  in
                (match uu____80 with
                 | (us1,t1) ->
                     let uu____93 =
                       let uu____98 =
                         let uu____105 =
                           FStar_TypeChecker_Env.push_univ_vars env us1  in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____105 t1
                          in
                       match uu____98 with
                       | (t2,lc,g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ)))
                        in
                     (match uu____93 with
                      | (t2,ty) ->
                          let uu____122 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2
                             in
                          (match uu____122 with
                           | (g_us,t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty
                                  in
                               (if (FStar_List.length g_us) <> n
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n  in
                                     let uu____147 =
                                       let uu____149 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length
                                          in
                                       FStar_All.pipe_right uu____149
                                         FStar_Util.string_of_int
                                        in
                                     let uu____156 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3)
                                        in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____145 uu____147
                                       uu____156
                                      in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____165 ->
                                        let uu____166 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1  ->
                                                  fun u2  ->
                                                    let uu____173 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2
                                                       in
                                                    uu____173 =
                                                      Prims.int_zero) us1
                                               g_us)
                                           in
                                        if uu____166
                                        then ()
                                        else
                                          (let uu____180 =
                                             let uu____186 =
                                               let uu____188 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1
                                                  in
                                               let uu____190 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us
                                                  in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____188
                                                 uu____190
                                                in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____186)
                                              in
                                           FStar_Errors.raise_error uu____180
                                             t3.FStar_Syntax_Syntax.pos)))
                                else ();
                                (g_us, t3, ty1)))))
  
let (pure_wp_uvar :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      Prims.string ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun t  ->
      fun reason  ->
        fun r  ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____229 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid
                 in
              FStar_All.pipe_right uu____229 FStar_Util.must  in
            let uu____234 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts  in
            match uu____234 with
            | (uu____239,pure_wp_t) ->
                let uu____241 =
                  let uu____242 =
                    FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                  [uu____242]  in
                FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____241 r
             in
          let uu____275 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t
             in
          match uu____275 with
          | (pure_wp_uvar,uu____293,guard_wp) -> (pure_wp_uvar, guard_wp)
  
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        (let uu____328 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffectsTc")
            in
         if uu____328
         then
           let uu____333 = FStar_Syntax_Print.term_to_string t  in
           let uu____335 =
             match k with
             | FStar_Pervasives_Native.None  -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1
              in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____333 uu____335
         else ());
        (let env1 =
           let uu___54_344 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___54_344.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___54_344.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___54_344.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___54_344.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___54_344.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___54_344.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___54_344.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___54_344.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___54_344.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___54_344.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___54_344.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___54_344.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___54_344.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___54_344.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___54_344.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___54_344.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___54_344.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict = true;
             FStar_TypeChecker_Env.is_iface =
               (uu___54_344.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___54_344.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___54_344.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___54_344.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___54_344.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___54_344.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___54_344.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___54_344.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___54_344.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___54_344.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___54_344.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___54_344.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___54_344.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___54_344.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___54_344.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___54_344.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___54_344.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___54_344.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___54_344.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___54_344.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___54_344.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___54_344.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___54_344.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___54_344.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___54_344.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___54_344.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___54_344.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___54_344.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___54_344.FStar_TypeChecker_Env.enable_defer_to_tac)
           }  in
         match k with
         | FStar_Pervasives_Native.None  ->
             let uu____346 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t
                in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____352 =
               FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k1  in
             ())
  
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun quals  ->
        (let uu____374 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffectsTc")
            in
         if uu____374
         then
           let uu____379 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____379
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____397 =
             let uu____403 =
               let uu____405 =
                 let uu____407 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 Prims.op_Hat uu____407 ")"  in
               Prims.op_Hat "Binders are not supported for layered effects ("
                 uu____405
                in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____403)  in
           let uu____412 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error uu____397 uu____412)
        else ();
        (let log_combinator s uu____438 =
           match uu____438 with
           | (us,t,ty) ->
               let uu____467 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffectsTc")
                  in
               if uu____467
               then
                 let uu____472 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____474 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____480 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____472 s
                   uu____474 uu____480
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____505 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____505
             (fun uu____522  ->
                match uu____522 with
                | (t,u) ->
                    let uu____533 =
                      let uu____534 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____534
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____533, u))
            in
         let fresh_x_a x a =
           let uu____548 =
             let uu____549 =
               let uu____550 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____550 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____549
              in
           FStar_All.pipe_right uu____548 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           let uu____584 =
             FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
           check_and_gen env0 uu____584  in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____604 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____604 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____628 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____628 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____648 = fresh_a_and_u_a "a"  in
                    (match uu____648 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____669 =
                             let uu____670 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____670
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____669
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____701 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____701  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____706 =
                             let uu____709 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____709
                              in
                           (sig_us, uu____706, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____718 =
            let repr_ts =
              let uu____740 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____740 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____768 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____768 with
            | (repr_us,repr_t,repr_ty) ->
                let underlying_effect_lid =
                  let repr_t1 =
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.UnfoldUntil
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_zero);
                      FStar_TypeChecker_Env.AllowUnboundUniverses] env0
                      repr_t
                     in
                  let uu____799 =
                    let uu____800 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____800.FStar_Syntax_Syntax.n  in
                  match uu____799 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____803,t,uu____805) ->
                      let uu____830 =
                        let uu____831 = FStar_Syntax_Subst.compress t  in
                        uu____831.FStar_Syntax_Syntax.n  in
                      (match uu____830 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____834,c) ->
                           let uu____856 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____856
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____859 ->
                           let uu____860 =
                             let uu____866 =
                               let uu____868 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____871 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____868 uu____871
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____866)
                              in
                           FStar_Errors.raise_error uu____860 r)
                  | uu____875 ->
                      let uu____876 =
                        let uu____882 =
                          let uu____884 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____887 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____884 uu____887
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____882)  in
                      FStar_Errors.raise_error uu____876 r
                   in
                ((let uu____892 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____898 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____898)
                     in
                  if uu____892
                  then
                    let uu____901 =
                      let uu____907 =
                        let uu____909 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____912 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____909 uu____912
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____907)
                       in
                    FStar_Errors.raise_error uu____901 r
                  else ());
                 (let uu____919 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____919 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____943 = fresh_a_and_u_a "a"  in
                      (match uu____943 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____969 = signature  in
                               match uu____969 with
                               | (us1,t,uu____984) -> (us1, t)  in
                             let uu____1001 =
                               let uu____1002 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____1002
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____1001
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1029 =
                               let uu____1032 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1032
                                 (fun uu____1045  ->
                                    match uu____1045 with
                                    | (t,u1) ->
                                        let uu____1052 =
                                          let uu____1055 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1055
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1052)
                                in
                             FStar_Syntax_Util.arrow bs uu____1029  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1058 =
                               let uu____1071 =
                                 let uu____1074 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1074
                                  in
                               (repr_us, repr_t, uu____1071)  in
                             (uu____1058, underlying_effect_lid))))))
             in
          match uu____718 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1147 = signature  in
                    match uu____1147 with | (us,t,uu____1162) -> (us, t)  in
                  let repr_ts =
                    let uu____1180 = repr  in
                    match uu____1180 with | (us,t,uu____1195) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n t r =
                  let uu____1245 =
                    let uu____1251 =
                      let uu____1253 =
                        FStar_Ident.string_of_lid
                          ed.FStar_Syntax_Syntax.mname
                         in
                      let uu____1255 = FStar_Util.string_of_int n  in
                      let uu____1257 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1259 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        uu____1253 comb uu____1255 uu____1257 uu____1259
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1251)  in
                  FStar_Errors.raise_error uu____1245 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1289 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1289 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1317 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1317 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1341 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1341 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1362 = fresh_a_and_u_a "a"  in
                             match uu____1362 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1393 =
                                     let uu____1394 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1394.FStar_Syntax_Syntax.n  in
                                   match uu____1393 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1406) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1434 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1434 with
                                        | (a',uu____1444)::(x',uu____1446)::bs1
                                            ->
                                            let uu____1476 =
                                              let uu____1477 =
                                                let uu____1482 =
                                                  let uu____1485 =
                                                    let uu____1486 =
                                                      let uu____1493 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1493)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1486
                                                     in
                                                  [uu____1485]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1482
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1477
                                               in
                                            let uu____1500 =
                                              let uu____1513 =
                                                let uu____1516 =
                                                  let uu____1517 =
                                                    let uu____1524 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1524)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1517
                                                   in
                                                [uu____1516]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1513
                                               in
                                            FStar_All.pipe_right uu____1476
                                              uu____1500)
                                   | uu____1539 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1563 =
                                   let uu____1568 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1569 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1568 u_a uu____1569  in
                                 (match uu____1563 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1589 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1589
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1594 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1594);
                                       (let uu____1595 =
                                          let uu____1598 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1598
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1595)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1627 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1627 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1655 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1655 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1679 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1679 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1700 = fresh_a_and_u_a "a"  in
                              match uu____1700 with
                              | (a,u_a) ->
                                  let uu____1720 = fresh_a_and_u_a "b"  in
                                  (match uu____1720 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1749 =
                                           let uu____1750 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1750.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1749 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1762) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1790 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1790 with
                                              | (a',uu____1800)::(b',uu____1802)::bs1
                                                  ->
                                                  let uu____1832 =
                                                    let uu____1833 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1833
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1899 =
                                                    let uu____1912 =
                                                      let uu____1915 =
                                                        let uu____1916 =
                                                          let uu____1923 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1923)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1916
                                                         in
                                                      let uu____1930 =
                                                        let uu____1933 =
                                                          let uu____1934 =
                                                            let uu____1941 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1941)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1934
                                                           in
                                                        [uu____1933]  in
                                                      uu____1915 ::
                                                        uu____1930
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1912
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1832 uu____1899)
                                         | uu____1956 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1980 =
                                         let uu____1991 =
                                           let uu____1996 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1997 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1996 u_a
                                             uu____1997
                                            in
                                         match uu____1991 with
                                         | (repr1,g) ->
                                             let uu____2012 =
                                               let uu____2019 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2019
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2012, g)
                                          in
                                       (match uu____1980 with
                                        | (f,guard_f) ->
                                            let uu____2059 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2072 =
                                                let uu____2077 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2096 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2077 u_b
                                                  uu____2096
                                                 in
                                              match uu____2072 with
                                              | (repr1,g) ->
                                                  let uu____2111 =
                                                    let uu____2118 =
                                                      let uu____2119 =
                                                        let uu____2120 =
                                                          let uu____2123 =
                                                            let uu____2126 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2126
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2123
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2120
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2119
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2118
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2111, g)
                                               in
                                            (match uu____2059 with
                                             | (g,guard_g) ->
                                                 let uu____2178 =
                                                   let uu____2183 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2184 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2183
                                                     u_b uu____2184
                                                    in
                                                 (match uu____2178 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2201 =
                                                        let uu____2206 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2207 =
                                                          let uu____2209 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname
                                                             in
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            uu____2209
                                                           in
                                                        pure_wp_uvar
                                                          uu____2206 repr1
                                                          uu____2207 r
                                                         in
                                                      (match uu____2201 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2229 =
                                                               let uu____2232
                                                                 =
                                                                 let uu____2233
                                                                   =
                                                                   let uu____2234
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2234]
                                                                    in
                                                                 let uu____2235
                                                                   =
                                                                   let uu____2246
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2246]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2233;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2235;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2232
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2229
                                                              in
                                                           let guard_eq =
                                                             FStar_TypeChecker_Rel.teq
                                                               env ty k
                                                              in
                                                           (FStar_List.iter
                                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                                 env)
                                                              [guard_f;
                                                              guard_g;
                                                              guard_repr;
                                                              g_pure_wp_uvar;
                                                              guard_eq];
                                                            (let uu____2305 =
                                                               let uu____2308
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2308
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2305)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2337 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2337 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2365 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2365 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2390 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc")
                             in
                          if uu____2390
                          then
                            let uu____2395 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2401 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2395 uu____2401
                          else ());
                         (let uu____2410 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2410 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2431 = fresh_a_and_u_a "a"  in
                                match uu____2431 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2460 =
                                        let uu____2461 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2461.FStar_Syntax_Syntax.n  in
                                      match uu____2460 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2473) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2501 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2501 with
                                           | (a',uu____2511)::bs1 ->
                                               let uu____2531 =
                                                 let uu____2532 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2532
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2630 =
                                                 let uu____2643 =
                                                   let uu____2646 =
                                                     let uu____2647 =
                                                       let uu____2654 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2654)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2647
                                                      in
                                                   [uu____2646]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2643
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2531 uu____2630)
                                      | uu____2669 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2687 =
                                      let uu____2698 =
                                        let uu____2703 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2704 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2703 u uu____2704
                                         in
                                      match uu____2698 with
                                      | (repr1,g) ->
                                          let uu____2719 =
                                            let uu____2726 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2726
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2719, g)
                                       in
                                    (match uu____2687 with
                                     | (f,guard_f) ->
                                         let uu____2766 =
                                           let uu____2771 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2772 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2771 u
                                             uu____2772
                                            in
                                         (match uu____2766 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2789 =
                                                let uu____2794 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2795 =
                                                  let uu____2797 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    uu____2797
                                                   in
                                                pure_wp_uvar uu____2794 ret_t
                                                  uu____2795 r
                                                 in
                                              (match uu____2789 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2815 =
                                                       let uu____2816 =
                                                         let uu____2817 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2817]  in
                                                       let uu____2818 =
                                                         let uu____2829 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2829]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2816;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2818;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2815
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2884 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffectsTc")
                                                        in
                                                     if uu____2884
                                                     then
                                                       let uu____2889 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type of subcomp before unification: %s\n"
                                                         uu____2889
                                                     else ());
                                                    (let guard_eq =
                                                       FStar_TypeChecker_Rel.teq
                                                         env ty k
                                                        in
                                                     FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env)
                                                       [guard_f;
                                                       guard_ret_t;
                                                       guard_wp;
                                                       guard_eq];
                                                     (let uu____2896 =
                                                        let uu____2899 =
                                                          let uu____2900 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2900
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2899
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2896)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else =
                     let if_then_else_ts =
                       let uu____2931 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2931 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2971 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2971 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2995 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2995 with
                          | (us,t) ->
                              let uu____3014 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____3014 with
                               | (uu____3031,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____3035 = fresh_a_and_u_a "a"  in
                                     match uu____3035 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3064 =
                                             let uu____3065 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3065.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3064 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3077) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3105 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3105 with
                                                | (a',uu____3115)::bs1 ->
                                                    let uu____3135 =
                                                      let uu____3136 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3136
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3234 =
                                                      let uu____3247 =
                                                        let uu____3250 =
                                                          let uu____3251 =
                                                            let uu____3258 =
                                                              let uu____3261
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3261
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3258)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3251
                                                           in
                                                        [uu____3250]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3247
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3135 uu____3234)
                                           | uu____3282 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3300 =
                                           let uu____3311 =
                                             let uu____3316 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3317 =
                                               let uu____3318 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3318
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3316 u_a
                                               uu____3317
                                              in
                                           match uu____3311 with
                                           | (repr1,g) ->
                                               let uu____3339 =
                                                 let uu____3346 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3346
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3339, g)
                                            in
                                         (match uu____3300 with
                                          | (f_bs,guard_f) ->
                                              let uu____3386 =
                                                let uu____3397 =
                                                  let uu____3402 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3403 =
                                                    let uu____3404 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3404
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3402 u_a
                                                    uu____3403
                                                   in
                                                match uu____3397 with
                                                | (repr1,g) ->
                                                    let uu____3425 =
                                                      let uu____3432 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3432
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3425, g)
                                                 in
                                              (match uu____3386 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3479 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3479
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3487 =
                                                     let uu____3492 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3511 =
                                                       let uu____3512 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3512
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3492
                                                       u_a uu____3511
                                                      in
                                                   (match uu____3487 with
                                                    | (t_body,guard_body) ->
                                                        let k =
                                                          FStar_Syntax_Util.abs
                                                            (FStar_List.append
                                                               bs
                                                               [f_bs;
                                                               g_bs;
                                                               p_b]) t_body
                                                            FStar_Pervasives_Native.None
                                                           in
                                                        let guard_eq =
                                                          FStar_TypeChecker_Rel.teq
                                                            env t k
                                                           in
                                                        (FStar_All.pipe_right
                                                           [guard_f;
                                                           guard_g;
                                                           guard_body;
                                                           guard_eq]
                                                           (FStar_List.iter
                                                              (FStar_TypeChecker_Rel.force_trivial_guard
                                                                 env));
                                                         (let uu____3572 =
                                                            let uu____3575 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3575
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3572,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else;
                   (let r =
                      let uu____3588 =
                        let uu____3591 =
                          let uu____3600 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3600 FStar_Util.must  in
                        FStar_All.pipe_right uu____3591
                          FStar_Pervasives_Native.snd
                         in
                      uu____3588.FStar_Syntax_Syntax.pos  in
                    let uu____3661 = if_then_else  in
                    match uu____3661 with
                    | (ite_us,ite_t,uu____3676) ->
                        let uu____3689 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3689 with
                         | (us,ite_t1) ->
                             let uu____3696 =
                               let uu____3711 =
                                 let uu____3712 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3712.FStar_Syntax_Syntax.n  in
                               match uu____3711 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3730,uu____3731) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3757 =
                                     let uu____3770 =
                                       let uu____3775 =
                                         let uu____3778 =
                                           let uu____3787 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3787
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3778
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3775
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3770
                                       (fun l  ->
                                          let uu____3943 = l  in
                                          match uu____3943 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3757 with
                                    | (f,g,p) ->
                                        let uu____4012 =
                                          let uu____4013 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____4013 bs1
                                           in
                                        let uu____4014 =
                                          let uu____4015 =
                                            let uu____4016 =
                                              let uu____4019 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.map
                                                     FStar_Pervasives_Native.fst)
                                                 in
                                              FStar_All.pipe_right uu____4019
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.bv_to_name)
                                               in
                                            FStar_All.pipe_right uu____4016
                                              (FStar_List.map
                                                 FStar_Syntax_Syntax.as_arg)
                                             in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            ite_t1 uu____4015 r
                                           in
                                        (uu____4012, uu____4014, f, g, p))
                               | uu____4050 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3696 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____4079 =
                                    let uu____4088 = stronger_repr  in
                                    match uu____4088 with
                                    | (uu____4109,subcomp_t,subcomp_ty) ->
                                        let uu____4124 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____4124 with
                                         | (uu____4137,subcomp_t1) ->
                                             let uu____4139 =
                                               let uu____4150 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____4150 with
                                               | (uu____4165,subcomp_ty1) ->
                                                   let uu____4167 =
                                                     let uu____4168 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____4168.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____4167 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4182) ->
                                                        let uu____4203 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        (match uu____4203
                                                         with
                                                         | (bs_except_last,last_b)
                                                             ->
                                                             let uu____4309 =
                                                               FStar_All.pipe_right
                                                                 bs_except_last
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             let uu____4336 =
                                                               let uu____4339
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   last_b
                                                                   FStar_List.hd
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____4339
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             (uu____4309,
                                                               uu____4336))
                                                    | uu____4382 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             (match uu____4139 with
                                              | (aqs_except_last,last_aq) ->
                                                  let aux t =
                                                    let tun_args =
                                                      FStar_All.pipe_right
                                                        aqs_except_last
                                                        (FStar_List.map
                                                           (fun aq  ->
                                                              (FStar_Syntax_Syntax.tun,
                                                                aq)))
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      subcomp_t1
                                                      (FStar_List.append
                                                         tun_args
                                                         [(t, last_aq)]) r
                                                     in
                                                  let uu____4493 = aux f_t
                                                     in
                                                  let uu____4496 = aux g_t
                                                     in
                                                  (uu____4493, uu____4496)))
                                     in
                                  (match uu____4079 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4513 =
                                         let aux t =
                                           let uu____4530 =
                                             let uu____4531 =
                                               let uu____4558 =
                                                 let uu____4575 =
                                                   let uu____4584 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       ite_t_applied
                                                      in
                                                   FStar_Util.Inr uu____4584
                                                    in
                                                 (uu____4575,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               (t, uu____4558,
                                                 FStar_Pervasives_Native.None)
                                                in
                                             FStar_Syntax_Syntax.Tm_ascribed
                                               uu____4531
                                              in
                                           FStar_Syntax_Syntax.mk uu____4530
                                             r
                                            in
                                         let uu____4625 = aux subcomp_f  in
                                         let uu____4626 = aux subcomp_g  in
                                         (uu____4625, uu____4626)  in
                                       (match uu____4513 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4630 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc")
                                                 in
                                              if uu____4630
                                              then
                                                let uu____4635 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4637 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4635 uu____4637
                                              else ());
                                             (let uu____4642 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4642 with
                                              | (uu____4649,uu____4650,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4653 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4653 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4655 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4655 with
                                                    | (uu____4662,uu____4663,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4667 =
                                                              let uu____4668
                                                                =
                                                                FStar_Syntax_Syntax.lid_as_fv
                                                                  FStar_Parser_Const.not_lid
                                                                  FStar_Syntax_Syntax.delta_constant
                                                                  FStar_Pervasives_Native.None
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____4668
                                                                FStar_Syntax_Syntax.fv_to_tm
                                                               in
                                                            let uu____4669 =
                                                              let uu____4670
                                                                =
                                                                FStar_All.pipe_right
                                                                  p_t
                                                                  FStar_Syntax_Syntax.as_arg
                                                                 in
                                                              [uu____4670]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              uu____4667
                                                              uu____4669 r
                                                             in
                                                          let uu____4703 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4703 g_g
                                                           in
                                                        FStar_TypeChecker_Rel.force_trivial_guard
                                                          env g_g1)))))))));
                   (let tc_action env act =
                      let env01 = env  in
                      let r =
                        (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                         in
                      if
                        (FStar_List.length
                           act.FStar_Syntax_Syntax.action_params)
                          <> Prims.int_zero
                      then
                        (let uu____4727 =
                           let uu____4733 =
                             let uu____4735 =
                               FStar_Ident.string_of_lid
                                 ed.FStar_Syntax_Syntax.mname
                                in
                             let uu____4737 =
                               FStar_Ident.string_of_lid
                                 act.FStar_Syntax_Syntax.action_name
                                in
                             let uu____4739 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               uu____4735 uu____4737 uu____4739
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4733)
                            in
                         FStar_Errors.raise_error uu____4727 r)
                      else ();
                      (let uu____4746 =
                         let uu____4751 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4751 with
                         | (usubst,us) ->
                             let uu____4774 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4775 =
                               let uu___452_4776 = act  in
                               let uu____4777 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4778 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___452_4776.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___452_4776.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___452_4776.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4777;
                                 FStar_Syntax_Syntax.action_typ = uu____4778
                               }  in
                             (uu____4774, uu____4775)
                          in
                       match uu____4746 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4782 =
                               let uu____4783 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4783.FStar_Syntax_Syntax.n  in
                             match uu____4782 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4809 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4809
                                 then
                                   let repr_ts =
                                     let uu____4813 = repr  in
                                     match uu____4813 with
                                     | (us,t,uu____4828) -> (us, t)  in
                                   let repr1 =
                                     let uu____4846 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4846
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4856 =
                                       let uu____4857 =
                                         FStar_Syntax_Syntax.as_arg
                                           ct.FStar_Syntax_Syntax.result_typ
                                          in
                                       uu____4857 ::
                                         (ct.FStar_Syntax_Syntax.effect_args)
                                        in
                                     FStar_Syntax_Syntax.mk_Tm_app repr1
                                       uu____4856 r
                                      in
                                   let c1 =
                                     let uu____4875 =
                                       let uu____4878 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4878
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4875
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4881 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4882 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4882 with
                            | (act_typ1,uu____4890,g_t) ->
                                let uu____4892 =
                                  let uu____4899 =
                                    let uu___477_4900 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___477_4900.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___477_4900.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___477_4900.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___477_4900.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___477_4900.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___477_4900.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___477_4900.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___477_4900.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___477_4900.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___477_4900.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___477_4900.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___477_4900.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___477_4900.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___477_4900.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___477_4900.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___477_4900.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___477_4900.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___477_4900.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___477_4900.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___477_4900.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___477_4900.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___477_4900.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___477_4900.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___477_4900.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___477_4900.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___477_4900.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___477_4900.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___477_4900.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___477_4900.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___477_4900.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___477_4900.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___477_4900.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___477_4900.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___477_4900.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___477_4900.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___477_4900.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___477_4900.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___477_4900.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___477_4900.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___477_4900.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___477_4900.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___477_4900.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___477_4900.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___477_4900.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___477_4900.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___477_4900.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4899
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4892 with
                                 | (act_defn,uu____4903,g_d) ->
                                     ((let uu____4906 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffectsTc")
                                          in
                                       if uu____4906
                                       then
                                         let uu____4911 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4913 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4911 uu____4913
                                       else ());
                                      (let uu____4918 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4926 =
                                           let uu____4927 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4927.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4926 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4937) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4960 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4960 with
                                              | (t,u) ->
                                                  let reason =
                                                    let uu____4975 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname
                                                       in
                                                    let uu____4977 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name
                                                       in
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      uu____4975 uu____4977
                                                     in
                                                  let uu____4980 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4980 with
                                                   | (a_tm,uu____5000,g_tm)
                                                       ->
                                                       let uu____5014 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____5014 with
                                                        | (repr1,g) ->
                                                            let uu____5027 =
                                                              let uu____5030
                                                                =
                                                                let uu____5033
                                                                  =
                                                                  let uu____5036
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____5036
                                                                    (
                                                                    fun
                                                                    uu____5039
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5039)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____5033
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5030
                                                               in
                                                            let uu____5040 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____5027,
                                                              uu____5040))))
                                         | uu____5043 ->
                                             let uu____5044 =
                                               let uu____5050 =
                                                 let uu____5052 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname
                                                    in
                                                 let uu____5054 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name
                                                    in
                                                 let uu____5056 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   uu____5052 uu____5054
                                                   uu____5056
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____5050)
                                                in
                                             FStar_Errors.raise_error
                                               uu____5044 r
                                          in
                                       match uu____4918 with
                                       | (k,g_k) ->
                                           ((let uu____5073 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffectsTc")
                                                in
                                             if uu____5073
                                             then
                                               let uu____5078 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____5078
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____5086 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc")
                                                 in
                                              if uu____5086
                                              then
                                                let uu____5091 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____5091
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____5104 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  let uu____5106 =
                                                    FStar_Ident.string_of_lid
                                                      act1.FStar_Syntax_Syntax.action_name
                                                     in
                                                  let uu____5108 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    uu____5104 uu____5106
                                                    uu____5108
                                                   in
                                                let repr_args t =
                                                  let uu____5129 =
                                                    let uu____5130 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5130.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5129 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,a::is) ->
                                                      let uu____5182 =
                                                        let uu____5183 =
                                                          FStar_Syntax_Subst.compress
                                                            head
                                                           in
                                                        uu____5183.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____5182 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____5192,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____5202 ->
                                                           let uu____5203 =
                                                             let uu____5209 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____5209)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5203 r)
                                                  | uu____5218 ->
                                                      let uu____5219 =
                                                        let uu____5225 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5225)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____5219 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____5235 =
                                                  let uu____5236 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____5236.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5235 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____5261 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____5261 with
                                                     | (bs1,c1) ->
                                                         let uu____5268 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____5268
                                                          with
                                                          | (us,a,is) ->
                                                              let ct =
                                                                {
                                                                  FStar_Syntax_Syntax.comp_univs
                                                                    = us;
                                                                  FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (
                                                                    ed.FStar_Syntax_Syntax.mname);
                                                                  FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                  FStar_Syntax_Syntax.effect_args
                                                                    = is;
                                                                  FStar_Syntax_Syntax.flags
                                                                    = []
                                                                }  in
                                                              let uu____5279
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5279))
                                                | uu____5282 ->
                                                    let uu____5283 =
                                                      let uu____5289 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____5289)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____5283 r
                                                 in
                                              (let uu____5293 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffectsTc")
                                                  in
                                               if uu____5293
                                               then
                                                 let uu____5298 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5298
                                               else ());
                                              (let act2 =
                                                 let uu____5304 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5304 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___550_5318 =
                                                         act1  in
                                                       let uu____5319 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___550_5318.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___550_5318.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___550_5318.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5319
                                                       }
                                                     else
                                                       (let uu____5322 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5329
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5329
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5322
                                                        then
                                                          let uu___555_5334 =
                                                            act1  in
                                                          let uu____5335 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___555_5334.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___555_5334.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___555_5334.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___555_5334.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5335
                                                          }
                                                        else
                                                          (let uu____5338 =
                                                             let uu____5344 =
                                                               let uu____5346
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   ed.FStar_Syntax_Syntax.mname
                                                                  in
                                                               let uu____5348
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   act1.FStar_Syntax_Syntax.action_name
                                                                  in
                                                               let uu____5350
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5352
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 uu____5346
                                                                 uu____5348
                                                                 uu____5350
                                                                 uu____5352
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5344)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5338 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5377 =
                      match uu____5377 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5422 =
                        let uu____5423 = tschemes_of repr  in
                        let uu____5428 = tschemes_of return_repr  in
                        let uu____5433 = tschemes_of bind_repr  in
                        let uu____5438 = tschemes_of stronger_repr  in
                        let uu____5443 = tschemes_of if_then_else  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5423;
                          FStar_Syntax_Syntax.l_return = uu____5428;
                          FStar_Syntax_Syntax.l_bind = uu____5433;
                          FStar_Syntax_Syntax.l_subcomp = uu____5438;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5443
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5422  in
                    let uu___564_5448 = ed  in
                    let uu____5449 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___564_5448.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___564_5448.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___564_5448.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___564_5448.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5456 = signature  in
                         match uu____5456 with | (us,t,uu____5471) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5449;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___564_5448.FStar_Syntax_Syntax.eff_attrs)
                    }))))))))
  
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0  ->
    fun ed  ->
      fun _quals  ->
        (let uu____5509 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5509
         then
           let uu____5514 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5514
         else ());
        (let uu____5520 =
           let uu____5525 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5525 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5549 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5549  in
               let uu____5550 =
                 let uu____5557 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5557 bs  in
               (match uu____5550 with
                | (bs1,uu____5563,uu____5564) ->
                    let uu____5565 =
                      let tmp_t =
                        let uu____5575 =
                          let uu____5578 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5583  ->
                                 FStar_Pervasives_Native.Some uu____5583)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5578
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5575  in
                      let uu____5584 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5584 with
                      | (us,tmp_t1) ->
                          let uu____5601 =
                            let uu____5602 =
                              let uu____5603 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5603
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5602
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5601)
                       in
                    (match uu____5565 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5640 ->
                              let uu____5643 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5650 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5650 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5643
                              then (us, bs2)
                              else
                                (let uu____5661 =
                                   let uu____5667 =
                                     let uu____5669 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname
                                        in
                                     let uu____5671 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5673 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5669 uu____5671 uu____5673
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5667)
                                    in
                                 let uu____5677 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5661
                                   uu____5677))))
            in
         match uu____5520 with
         | (us,bs) ->
             let ed1 =
               let uu___598_5685 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___598_5685.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___598_5685.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___598_5685.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___598_5685.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___598_5685.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___598_5685.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5686 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5686 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5705 =
                    let uu____5710 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5710  in
                  (match uu____5705 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5731 =
                           match uu____5731 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5751 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5751 t  in
                               let uu____5760 =
                                 let uu____5761 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5761 t1  in
                               (us1, uu____5760)
                            in
                         let uu___612_5766 = ed1  in
                         let uu____5767 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5768 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5769 =
                           FStar_List.map
                             (fun a  ->
                                let uu___615_5777 = a  in
                                let uu____5778 =
                                  let uu____5779 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5779  in
                                let uu____5790 =
                                  let uu____5791 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5791  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___615_5777.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___615_5777.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___615_5777.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___615_5777.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5778;
                                  FStar_Syntax_Syntax.action_typ = uu____5790
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___612_5766.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___612_5766.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___612_5766.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___612_5766.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5767;
                           FStar_Syntax_Syntax.combinators = uu____5768;
                           FStar_Syntax_Syntax.actions = uu____5769;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___612_5766.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5803 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5803
                         then
                           let uu____5808 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5808
                         else ());
                        (let env =
                           let uu____5815 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5815
                             ed_bs
                            in
                         let check_and_gen' comb n env_opt uu____5850 k =
                           match uu____5850 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5870 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5870 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5879 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5879 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5880 =
                                            let uu____5887 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5887 t1
                                             in
                                          (match uu____5880 with
                                           | (t2,uu____5889,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5892 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5892 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5908 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname
                                                  in
                                               let uu____5910 =
                                                 FStar_Util.string_of_int n
                                                  in
                                               let uu____5912 =
                                                 let uu____5914 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5914
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5908 comb uu____5910
                                                 uu____5912
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5929 ->
                                               let uu____5930 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5937 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5937 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5930
                                               then (g_us, t3)
                                               else
                                                 (let uu____5948 =
                                                    let uu____5954 =
                                                      let uu____5956 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      let uu____5958 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5960 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5956 comb
                                                        uu____5958 uu____5960
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5954)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5948
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5968 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5968
                          then
                            let uu____5973 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5973
                          else ());
                         (let fresh_a_and_wp uu____5989 =
                            let fail t =
                              let uu____6002 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____6002
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____6018 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____6018 with
                            | (uu____6029,signature1) ->
                                let uu____6031 =
                                  let uu____6032 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____6032.FStar_Syntax_Syntax.n  in
                                (match uu____6031 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____6042) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____6071)::(wp,uu____6073)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6102 -> fail signature1)
                                 | uu____6103 -> fail signature1)
                             in
                          let log_combinator s ts =
                            let uu____6117 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____6117
                            then
                              let uu____6122 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname
                                 in
                              let uu____6124 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____6122 s uu____6124
                            else ()  in
                          let ret_wp =
                            let uu____6130 = fresh_a_and_wp ()  in
                            match uu____6130 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____6146 =
                                    let uu____6155 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____6162 =
                                      let uu____6171 =
                                        let uu____6178 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6178
                                         in
                                      [uu____6171]  in
                                    uu____6155 :: uu____6162  in
                                  let uu____6197 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____6146
                                    uu____6197
                                   in
                                let uu____6200 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6200
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6214 = fresh_a_and_wp ()  in
                             match uu____6214 with
                             | (a,wp_sort_a) ->
                                 let uu____6227 = fresh_a_and_wp ()  in
                                 (match uu____6227 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6243 =
                                          let uu____6252 =
                                            let uu____6259 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6259
                                             in
                                          [uu____6252]  in
                                        let uu____6272 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6243
                                          uu____6272
                                         in
                                      let k =
                                        let uu____6278 =
                                          let uu____6287 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6294 =
                                            let uu____6303 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6310 =
                                              let uu____6319 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6326 =
                                                let uu____6335 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6342 =
                                                  let uu____6351 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6351]  in
                                                uu____6335 :: uu____6342  in
                                              uu____6319 :: uu____6326  in
                                            uu____6303 :: uu____6310  in
                                          uu____6287 :: uu____6294  in
                                        let uu____6394 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6278
                                          uu____6394
                                         in
                                      let uu____6397 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6397
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6411 = fresh_a_and_wp ()  in
                              match uu____6411 with
                              | (a,wp_sort_a) ->
                                  let uu____6424 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6424 with
                                   | (t,uu____6430) ->
                                       let k =
                                         let uu____6434 =
                                           let uu____6443 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6450 =
                                             let uu____6459 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6466 =
                                               let uu____6475 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6475]  in
                                             uu____6459 :: uu____6466  in
                                           uu____6443 :: uu____6450  in
                                         let uu____6506 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6434
                                           uu____6506
                                          in
                                       let uu____6509 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6509
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6523 = fresh_a_and_wp ()  in
                               match uu____6523 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6537 =
                                       let uu____6540 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6540
                                        in
                                     let uu____6541 =
                                       let uu____6542 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6542
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6537
                                       uu____6541
                                      in
                                   let k =
                                     let uu____6554 =
                                       let uu____6563 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6570 =
                                         let uu____6579 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6586 =
                                           let uu____6595 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6602 =
                                             let uu____6611 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6611]  in
                                           uu____6595 :: uu____6602  in
                                         uu____6579 :: uu____6586  in
                                       uu____6563 :: uu____6570  in
                                     let uu____6648 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6554
                                       uu____6648
                                      in
                                   let uu____6651 =
                                     let uu____6656 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6656
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6651
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6688 = fresh_a_and_wp ()  in
                                match uu____6688 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6704 =
                                        let uu____6713 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6720 =
                                          let uu____6729 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6729]  in
                                        uu____6713 :: uu____6720  in
                                      let uu____6754 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6704
                                        uu____6754
                                       in
                                    let uu____6757 =
                                      let uu____6762 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6762
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6757
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6778 = fresh_a_and_wp ()  in
                                 match uu____6778 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6792 =
                                         let uu____6795 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6795
                                          in
                                       let uu____6796 =
                                         let uu____6797 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6797
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6792
                                         uu____6796
                                        in
                                     let wp_sort_b_a =
                                       let uu____6809 =
                                         let uu____6818 =
                                           let uu____6825 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6825
                                            in
                                         [uu____6818]  in
                                       let uu____6838 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6809
                                         uu____6838
                                        in
                                     let k =
                                       let uu____6844 =
                                         let uu____6853 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6860 =
                                           let uu____6869 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6876 =
                                             let uu____6885 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6885]  in
                                           uu____6869 :: uu____6876  in
                                         uu____6853 :: uu____6860  in
                                       let uu____6916 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6844
                                         uu____6916
                                        in
                                     let uu____6919 =
                                       let uu____6924 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6924
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6919
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6940 = fresh_a_and_wp ()  in
                                  match uu____6940 with
                                  | (a,wp_sort_a) ->
                                      let uu____6953 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6953 with
                                       | (t,uu____6959) ->
                                           let k =
                                             let uu____6963 =
                                               let uu____6972 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6979 =
                                                 let uu____6988 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6988]  in
                                               uu____6972 :: uu____6979  in
                                             let uu____7013 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6963 uu____7013
                                              in
                                           let trivial =
                                             let uu____7017 =
                                               let uu____7022 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7022 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____7017
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____7037 =
                                  let uu____7054 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____7054 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____7083 ->
                                      let repr =
                                        let uu____7087 = fresh_a_and_wp ()
                                           in
                                        match uu____7087 with
                                        | (a,wp_sort_a) ->
                                            let uu____7100 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____7100 with
                                             | (t,uu____7106) ->
                                                 let k =
                                                   let uu____7110 =
                                                     let uu____7119 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____7126 =
                                                       let uu____7135 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____7135]  in
                                                     uu____7119 :: uu____7126
                                                      in
                                                   let uu____7160 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7110 uu____7160
                                                    in
                                                 let uu____7163 =
                                                   let uu____7168 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7168
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7163
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7212 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____7212 with
                                          | (uu____7219,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____7222 =
                                                let uu____7223 =
                                                  let uu____7240 =
                                                    let uu____7251 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7268 =
                                                      let uu____7279 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7279]  in
                                                    uu____7251 :: uu____7268
                                                     in
                                                  (repr2, uu____7240)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____7223
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7222
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7345 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7345 wp  in
                                        let destruct_repr t =
                                          let uu____7360 =
                                            let uu____7361 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7361.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7360 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7372,(t1,uu____7374)::
                                               (wp,uu____7376)::[])
                                              -> (t1, wp)
                                          | uu____7435 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7451 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7451
                                              FStar_Util.must
                                             in
                                          let uu____7478 = fresh_a_and_wp ()
                                             in
                                          match uu____7478 with
                                          | (a,uu____7486) ->
                                              let x_a =
                                                let uu____7492 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7492
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7498 =
                                                    let uu____7499 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7499
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____7508 =
                                                    let uu____7509 =
                                                      let uu____7518 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7518
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7527 =
                                                      let uu____7538 =
                                                        let uu____7547 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7547
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7538]  in
                                                    uu____7509 :: uu____7527
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7498 uu____7508
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7583 =
                                                  let uu____7592 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7599 =
                                                    let uu____7608 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7608]  in
                                                  uu____7592 :: uu____7599
                                                   in
                                                let uu____7633 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7583 uu____7633
                                                 in
                                              let uu____7636 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7636 with
                                               | (k1,uu____7644,uu____7645)
                                                   ->
                                                   let env1 =
                                                     let uu____7649 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7649
                                                      in
                                                   check_and_gen'
                                                     "return_repr"
                                                     Prims.int_one env1
                                                     return_repr_ts
                                                     (FStar_Pervasives_Native.Some
                                                        k1))
                                           in
                                        log_combinator "return_repr"
                                          return_repr;
                                        (let bind_repr =
                                           let bind_repr_ts =
                                             let uu____7662 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7662
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7700 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7700
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7701 = fresh_a_and_wp ()
                                              in
                                           match uu____7701 with
                                           | (a,wp_sort_a) ->
                                               let uu____7714 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7714 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7730 =
                                                        let uu____7739 =
                                                          let uu____7746 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7746
                                                           in
                                                        [uu____7739]  in
                                                      let uu____7759 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7730 uu____7759
                                                       in
                                                    let wp_f =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_f"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a
                                                       in
                                                    let wp_g =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_g"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a_b
                                                       in
                                                    let x_a =
                                                      let uu____7767 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7767
                                                       in
                                                    let wp_g_x =
                                                      let uu____7770 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g
                                                         in
                                                      let uu____7771 =
                                                        let uu____7772 =
                                                          let uu____7781 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7781
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7772]  in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7770 uu____7771
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7810 =
                                                          let uu____7811 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7811
                                                            FStar_Pervasives_Native.snd
                                                           in
                                                        let uu____7820 =
                                                          let uu____7821 =
                                                            let uu____7824 =
                                                              let uu____7827
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a
                                                                 in
                                                              let uu____7828
                                                                =
                                                                let uu____7831
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b
                                                                   in
                                                                let uu____7832
                                                                  =
                                                                  let uu____7835
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  let uu____7836
                                                                    =
                                                                    let uu____7839
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7839]
                                                                     in
                                                                  uu____7835
                                                                    ::
                                                                    uu____7836
                                                                   in
                                                                uu____7831 ::
                                                                  uu____7832
                                                                 in
                                                              uu____7827 ::
                                                                uu____7828
                                                               in
                                                            r :: uu____7824
                                                             in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7821
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7810
                                                          uu____7820
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7857 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7857
                                                      then
                                                        let uu____7868 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7875 =
                                                          let uu____7884 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7884]  in
                                                        uu____7868 ::
                                                          uu____7875
                                                      else []  in
                                                    let k =
                                                      let uu____7920 =
                                                        let uu____7929 =
                                                          let uu____7938 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7945 =
                                                            let uu____7954 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7954]  in
                                                          uu____7938 ::
                                                            uu____7945
                                                           in
                                                        let uu____7979 =
                                                          let uu____7988 =
                                                            let uu____7997 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____8004 =
                                                              let uu____8013
                                                                =
                                                                let uu____8020
                                                                  =
                                                                  let uu____8021
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____8021
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____8020
                                                                 in
                                                              let uu____8022
                                                                =
                                                                let uu____8031
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____8038
                                                                  =
                                                                  let uu____8047
                                                                    =
                                                                    let uu____8054
                                                                    =
                                                                    let uu____8055
                                                                    =
                                                                    let uu____8064
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____8064]
                                                                     in
                                                                    let uu____8083
                                                                    =
                                                                    let uu____8086
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____8086
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____8055
                                                                    uu____8083
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____8054
                                                                     in
                                                                  [uu____8047]
                                                                   in
                                                                uu____8031 ::
                                                                  uu____8038
                                                                 in
                                                              uu____8013 ::
                                                                uu____8022
                                                               in
                                                            uu____7997 ::
                                                              uu____8004
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7988
                                                           in
                                                        FStar_List.append
                                                          uu____7929
                                                          uu____7979
                                                         in
                                                      let uu____8131 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7920 uu____8131
                                                       in
                                                    let uu____8134 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____8134 with
                                                     | (k1,uu____8142,uu____8143)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___810_8153
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___810_8153.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____8155 
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8155)
                                                            in
                                                         check_and_gen'
                                                           "bind_repr"
                                                           (Prims.of_int (2))
                                                           env2 bind_repr_ts
                                                           (FStar_Pervasives_Native.Some
                                                              k1)))
                                            in
                                         log_combinator "bind_repr" bind_repr;
                                         (let actions =
                                            let check_action act =
                                              if
                                                (FStar_List.length
                                                   act.FStar_Syntax_Syntax.action_params)
                                                  <> Prims.int_zero
                                              then
                                                failwith
                                                  "tc_eff_decl: expected action_params to be empty"
                                              else ();
                                              (let uu____8182 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8196 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____8196 with
                                                    | (usubst,uvs) ->
                                                        let uu____8219 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____8220 =
                                                          let uu___823_8221 =
                                                            act  in
                                                          let uu____8222 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____8223 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___823_8221.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___823_8221.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___823_8221.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8222;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8223
                                                          }  in
                                                        (uu____8219,
                                                          uu____8220))
                                                  in
                                               match uu____8182 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____8227 =
                                                       let uu____8228 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____8228.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____8227 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____8254 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____8254
                                                         then
                                                           let uu____8257 =
                                                             let uu____8260 =
                                                               let uu____8261
                                                                 =
                                                                 let uu____8262
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8262
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8261
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8260
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8257
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8285 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8286 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8286 with
                                                    | (act_typ1,uu____8294,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___840_8297 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___840_8297.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          }  in
                                                        ((let uu____8300 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8300
                                                          then
                                                            let uu____8304 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8306 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8308 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8304
                                                              uu____8306
                                                              uu____8308
                                                          else ());
                                                         (let uu____8313 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8313
                                                          with
                                                          | (act_defn,uu____8321,g_a)
                                                              ->
                                                              let act_defn1 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                  env1
                                                                  act_defn
                                                                 in
                                                              let act_typ2 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                  FStar_TypeChecker_Env.Eager_unfolding;
                                                                  FStar_TypeChecker_Env.Beta]
                                                                  env1
                                                                  act_typ1
                                                                 in
                                                              let uu____8325
                                                                =
                                                                let act_typ3
                                                                  =
                                                                  FStar_Syntax_Subst.compress
                                                                    act_typ2
                                                                   in
                                                                match 
                                                                  act_typ3.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8361
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8361
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8373)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8380
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8380
                                                                     in
                                                                    let uu____8383
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8383
                                                                    with
                                                                    | 
                                                                    (k1,uu____8397,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8401
                                                                    ->
                                                                    let uu____8402
                                                                    =
                                                                    let uu____8408
                                                                    =
                                                                    let uu____8410
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8412
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8410
                                                                    uu____8412
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8408)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8402
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8325
                                                               with
                                                               | (expected_k,g_k)
                                                                   ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k
                                                                     in
                                                                   ((
                                                                    let uu____8430
                                                                    =
                                                                    let uu____8431
                                                                    =
                                                                    let uu____8432
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8432
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8431
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8430);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8434
                                                                    =
                                                                    let uu____8435
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8435.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8434
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8460
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8460
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8467
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8467
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8487
                                                                    =
                                                                    let uu____8488
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8488]
                                                                     in
                                                                    let uu____8489
                                                                    =
                                                                    let uu____8500
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8500]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8487;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8489;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8525
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8525))
                                                                    | 
                                                                    uu____8528
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8530
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8552
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8552))
                                                                     in
                                                                    match uu____8530
                                                                    with
                                                                    | 
                                                                    (univs,act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3
                                                                     in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs
                                                                    act_typ4
                                                                     in
                                                                    let uu___890_8571
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___890_8571.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___890_8571.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___890_8571.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    })))))))
                                               in
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.actions
                                              (FStar_List.map check_action)
                                             in
                                          ((FStar_Pervasives_Native.Some repr),
                                            (FStar_Pervasives_Native.Some
                                               return_repr),
                                            (FStar_Pervasives_Native.Some
                                               bind_repr), actions)))))
                                   in
                                match uu____7037 with
                                | (repr,return_repr,bind_repr,actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts
                                         in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs
                                         in
                                      let uu____8614 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8614 ts1
                                       in
                                    let combinators =
                                      {
                                        FStar_Syntax_Syntax.ret_wp = ret_wp;
                                        FStar_Syntax_Syntax.bind_wp = bind_wp;
                                        FStar_Syntax_Syntax.stronger =
                                          stronger;
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else;
                                        FStar_Syntax_Syntax.ite_wp = ite_wp;
                                        FStar_Syntax_Syntax.close_wp =
                                          close_wp;
                                        FStar_Syntax_Syntax.trivial = trivial;
                                        FStar_Syntax_Syntax.repr = repr;
                                        FStar_Syntax_Syntax.return_repr =
                                          return_repr;
                                        FStar_Syntax_Syntax.bind_repr =
                                          bind_repr
                                      }  in
                                    let combinators1 =
                                      FStar_Syntax_Util.apply_wp_eff_combinators
                                        cl combinators
                                       in
                                    let combinators2 =
                                      match ed2.FStar_Syntax_Syntax.combinators
                                      with
                                      | FStar_Syntax_Syntax.Primitive_eff
                                          uu____8626 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8627 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8628 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___910_8631 = ed2  in
                                      let uu____8632 = cl signature  in
                                      let uu____8633 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___913_8641 = a  in
                                             let uu____8642 =
                                               let uu____8643 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8643
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8668 =
                                               let uu____8669 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8669
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___913_8641.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___913_8641.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___913_8641.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___913_8641.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8642;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8668
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___910_8631.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___910_8631.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___910_8631.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___910_8631.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8632;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8633;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___910_8631.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8695 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8695
                                      then
                                        let uu____8700 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8700
                                      else ());
                                     ed3)))))))))))))
  
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun ed  ->
      fun quals  ->
        let uu____8726 =
          let uu____8741 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8741 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8726 env ed quals
  
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env  ->
    fun m  ->
      fun s  ->
        let fail uu____8791 =
          let uu____8792 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8798 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8792 uu____8798  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8842)::(wp,uu____8844)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8873 -> fail ())
        | uu____8874 -> fail ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub  ->
      (let uu____8887 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc")
          in
       if uu____8887
       then
         let uu____8892 = FStar_Syntax_Print.sub_eff_to_string sub  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8892
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8909 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8909.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.target
           in
        let uu____8921 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8925 =
                let uu____8926 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8926 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8925
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8935 =
                   let uu____8936 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8936 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8935
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8944 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8944))
           in
        if uu____8921
        then
          let uu____8947 =
            let uu____8953 =
              let uu____8955 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8958 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8955 uu____8958
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8953)  in
          FStar_Errors.raise_error uu____8947 r
        else ());
       (let uu____8965 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8965 with
        | (us,lift,lift_ty) ->
            ((let uu____8979 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffectsTc")
                 in
              if uu____8979
              then
                let uu____8984 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8990 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8984 uu____8990
              else ());
             (let uu____8999 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8999 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____9017 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.source
                         in
                      let uu____9019 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.target
                         in
                      let uu____9021 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____9017 uu____9019 s uu____9021
                       in
                    let uu____9024 =
                      let uu____9031 =
                        let uu____9036 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____9036
                          (fun uu____9053  ->
                             match uu____9053 with
                             | (t,u) ->
                                 let uu____9064 =
                                   let uu____9065 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____9065
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____9064, u))
                         in
                      match uu____9031 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____9084 =
                              let uu____9085 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____9085.FStar_Syntax_Syntax.n  in
                            match uu____9084 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____9097)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____9125 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____9125 with
                                 | (a',uu____9135)::bs1 ->
                                     let uu____9155 =
                                       let uu____9156 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____9156
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____9222 =
                                       let uu____9235 =
                                         let uu____9238 =
                                           let uu____9239 =
                                             let uu____9246 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____9246)  in
                                           FStar_Syntax_Syntax.NT uu____9239
                                            in
                                         [uu____9238]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____9235
                                        in
                                     FStar_All.pipe_right uu____9155
                                       uu____9222)
                            | uu____9261 ->
                                let uu____9262 =
                                  let uu____9268 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____9268)
                                   in
                                FStar_Errors.raise_error uu____9262 r
                             in
                          let uu____9280 =
                            let uu____9291 =
                              let uu____9296 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9303 =
                                let uu____9304 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9304
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9296 r sub.FStar_Syntax_Syntax.source
                                u_a uu____9303
                               in
                            match uu____9291 with
                            | (f_sort,g) ->
                                let uu____9325 =
                                  let uu____9332 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9332
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9325, g)
                             in
                          (match uu____9280 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9399 =
                                 let uu____9404 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9405 =
                                   let uu____9406 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9406
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9404 r
                                   sub.FStar_Syntax_Syntax.target u_a
                                   uu____9405
                                  in
                               (match uu____9399 with
                                | (repr,g_repr) ->
                                    let uu____9423 =
                                      let uu____9428 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9429 =
                                        let uu____9431 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9433 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9431 uu____9433
                                         in
                                      pure_wp_uvar uu____9428 repr uu____9429
                                        r
                                       in
                                    (match uu____9423 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9445 =
                                             let uu____9446 =
                                               let uu____9447 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9447]  in
                                             let uu____9448 =
                                               let uu____9459 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9459]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9446;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9448;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9445
                                            in
                                         let uu____9492 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9495 =
                                           let uu____9496 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9496 guard_wp
                                            in
                                         (uu____9492, uu____9495))))
                       in
                    match uu____9024 with
                    | (k,g_k) ->
                        ((let uu____9506 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffectsTc")
                             in
                          if uu____9506
                          then
                            let uu____9511 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9511
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9520 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc")
                              in
                           if uu____9520
                           then
                             let uu____9525 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9525
                           else ());
                          (let sub1 =
                             let uu___1006_9531 = sub  in
                             let uu____9532 =
                               let uu____9535 =
                                 let uu____9536 =
                                   let uu____9539 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9539
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9536)  in
                               FStar_Pervasives_Native.Some uu____9535  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1006_9531.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1006_9531.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9532;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9551 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc")
                               in
                            if uu____9551
                            then
                              let uu____9556 =
                                FStar_Syntax_Print.sub_eff_to_string sub1  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9556
                            else ());
                           sub1)))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub  ->
      fun r  ->
        let check_and_gen1 env1 t k =
          let uu____9593 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9593  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target
           in
        let uu____9596 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9596
        then tc_layered_lift env sub
        else
          (let uu____9603 =
             let uu____9610 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source
                in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9610
              in
           match uu____9603 with
           | (a,wp_a_src) ->
               let uu____9617 =
                 let uu____9624 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9624
                  in
               (match uu____9617 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9632 =
                        let uu____9635 =
                          let uu____9636 =
                            let uu____9643 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9643)  in
                          FStar_Syntax_Syntax.NT uu____9636  in
                        [uu____9635]  in
                      FStar_Syntax_Subst.subst uu____9632 wp_b_tgt  in
                    let expected_k =
                      let uu____9651 =
                        let uu____9660 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9667 =
                          let uu____9676 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9676]  in
                        uu____9660 :: uu____9667  in
                      let uu____9701 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9651 uu____9701  in
                    let repr_type eff_name a1 wp =
                      (let uu____9723 =
                         let uu____9725 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9725  in
                       if uu____9723
                       then
                         let uu____9728 =
                           let uu____9734 =
                             let uu____9736 =
                               FStar_Ident.string_of_lid eff_name  in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9736
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9734)
                            in
                         let uu____9740 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9728 uu____9740
                       else ());
                      (let uu____9743 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9743 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9776 =
                               let uu____9777 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9777
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9776
                              in
                           let uu____9784 =
                             let uu____9785 =
                               let uu____9802 =
                                 let uu____9813 =
                                   FStar_Syntax_Syntax.as_arg a1  in
                                 let uu____9822 =
                                   let uu____9833 =
                                     FStar_Syntax_Syntax.as_arg wp  in
                                   [uu____9833]  in
                                 uu____9813 :: uu____9822  in
                               (repr, uu____9802)  in
                             FStar_Syntax_Syntax.Tm_app uu____9785  in
                           let uu____9878 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Syntax_Syntax.mk uu____9784 uu____9878)
                       in
                    let uu____9879 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____10052 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____10063 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____10063 with
                              | (usubst,uvs1) ->
                                  let uu____10086 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____10087 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____10086, uu____10087)
                            else (env, lift_wp)  in
                          (match uu____10052 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10137 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10137))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10208 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10223 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10223 with
                              | (usubst,uvs) ->
                                  let uu____10248 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10248)
                            else ([], lift)  in
                          (match uu____10208 with
                           | (uvs,lift1) ->
                               ((let uu____10284 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10284
                                 then
                                   let uu____10288 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10288
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10294 =
                                   let uu____10301 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10301 lift1
                                    in
                                 match uu____10294 with
                                 | (lift2,comp,uu____10326) ->
                                     let uu____10327 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10327 with
                                      | (uu____10356,lift_wp,lift_elab) ->
                                          let lift_wp1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-wp" env lift_wp
                                             in
                                          let lift_elab1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-elab" env lift_elab
                                             in
                                          if
                                            (FStar_List.length uvs) =
                                              Prims.int_zero
                                          then
                                            let uu____10388 =
                                              let uu____10399 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10399
                                               in
                                            let uu____10416 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10388, uu____10416)
                                          else
                                            (let uu____10445 =
                                               let uu____10456 =
                                                 let uu____10465 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10465)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10456
                                                in
                                             let uu____10480 =
                                               let uu____10489 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10489)  in
                                             (uu____10445, uu____10480))))))
                       in
                    (match uu____9879 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1090_10553 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1090_10553.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1090_10553.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1090_10553.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1090_10553.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1090_10553.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1090_10553.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1090_10553.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1090_10553.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1090_10553.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1090_10553.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1090_10553.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1090_10553.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1090_10553.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1090_10553.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1090_10553.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1090_10553.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1090_10553.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1090_10553.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1090_10553.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1090_10553.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1090_10553.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1090_10553.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1090_10553.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1090_10553.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1090_10553.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1090_10553.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1090_10553.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1090_10553.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1090_10553.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1090_10553.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1090_10553.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1090_10553.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1090_10553.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1090_10553.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1090_10553.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1090_10553.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1090_10553.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1090_10553.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1090_10553.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1090_10553.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1090_10553.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1090_10553.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1090_10553.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1090_10553.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1090_10553.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1090_10553.FStar_TypeChecker_Env.enable_defer_to_tac)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10586 =
                                 let uu____10591 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10591 with
                                 | (usubst,uvs1) ->
                                     let uu____10614 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10615 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10614, uu____10615)
                                  in
                               (match uu____10586 with
                                | (env2,lift2) ->
                                    let uu____10620 =
                                      let uu____10627 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10627
                                       in
                                    (match uu____10620 with
                                     | (a1,wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1
                                            in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1
                                            in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a
                                            in
                                         let repr_f =
                                           repr_type
                                             sub.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ
                                            in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp)
                                              in
                                           let lift_wp_a =
                                             let uu____10653 =
                                               let uu____10654 =
                                                 let uu____10671 =
                                                   let uu____10682 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ
                                                      in
                                                   let uu____10691 =
                                                     let uu____10702 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ
                                                        in
                                                     [uu____10702]  in
                                                   uu____10682 :: uu____10691
                                                    in
                                                 (lift_wp1, uu____10671)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____10654
                                                in
                                             let uu____10747 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10653 uu____10747
                                              in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10751 =
                                             let uu____10760 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10767 =
                                               let uu____10776 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10783 =
                                                 let uu____10792 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10792]  in
                                               uu____10776 :: uu____10783  in
                                             uu____10760 :: uu____10767  in
                                           let uu____10823 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10751 uu____10823
                                            in
                                         let uu____10826 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10826 with
                                          | (expected_k2,uu____10836,uu____10837)
                                              ->
                                              let lift3 =
                                                if
                                                  (FStar_List.length uvs) =
                                                    Prims.int_zero
                                                then
                                                  check_and_gen1 env2 lift2
                                                    expected_k2
                                                else
                                                  (let lift3 =
                                                     FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                                       env2 lift2 expected_k2
                                                      in
                                                   let uu____10845 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10845))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10853 =
                             let uu____10855 =
                               let uu____10857 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10857
                                 FStar_List.length
                                in
                             uu____10855 <> Prims.int_one  in
                           if uu____10853
                           then
                             let uu____10880 =
                               let uu____10886 =
                                 let uu____10888 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10890 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10892 =
                                   let uu____10894 =
                                     let uu____10896 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10896
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10894
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10888 uu____10890 uu____10892
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10886)
                                in
                             FStar_Errors.raise_error uu____10880 r
                           else ());
                          (let uu____10923 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10926 =
                                  let uu____10928 =
                                    let uu____10931 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10931
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10928
                                    FStar_List.length
                                   in
                                uu____10926 <> Prims.int_one)
                              in
                           if uu____10923
                           then
                             let uu____10970 =
                               let uu____10976 =
                                 let uu____10978 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10980 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10982 =
                                   let uu____10984 =
                                     let uu____10986 =
                                       let uu____10989 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10989
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10986
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10984
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10978 uu____10980 uu____10982
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10976)
                                in
                             FStar_Errors.raise_error uu____10970 r
                           else ());
                          (let uu___1127_11031 = sub  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1127_11031.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1127_11031.FStar_Syntax_Syntax.target);
                             FStar_Syntax_Syntax.lift_wp =
                               (FStar_Pervasives_Native.Some lift_wp);
                             FStar_Syntax_Syntax.lift = lift1
                           })))))
  
let (tc_effect_abbrev :
  FStar_TypeChecker_Env.env ->
    (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
      FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) ->
      FStar_Range.range ->
        (FStar_Ident.lident * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun env  ->
    fun uu____11062  ->
      fun r  ->
        match uu____11062 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____11085 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11113 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11113 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11144 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11144 c  in
                     let uu____11153 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11153, uvs1, tps1, c1))
               in
            (match uu____11085 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11173 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11173 with
                  | (tps2,c2) ->
                      let uu____11188 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11188 with
                       | (tps3,env3,us) ->
                           let uu____11206 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11206 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11232)::uu____11233 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11252 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11260 =
                                    let uu____11262 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11262  in
                                  if uu____11260
                                  then
                                    let uu____11265 =
                                      let uu____11271 =
                                        let uu____11273 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11275 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11273 uu____11275
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11271)
                                       in
                                    FStar_Errors.raise_error uu____11265 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11283 =
                                    let uu____11284 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11284
                                     in
                                  match uu____11283 with
                                  | (uvs2,t) ->
                                      let uu____11313 =
                                        let uu____11318 =
                                          let uu____11331 =
                                            let uu____11332 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11332.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11331)  in
                                        match uu____11318 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11347,c5)) -> ([], c5)
                                        | (uu____11389,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11428 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11313 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11460 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11460 with
                                               | (uu____11465,t1) ->
                                                   let uu____11467 =
                                                     let uu____11473 =
                                                       let uu____11475 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11477 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11481 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11475
                                                         uu____11477
                                                         uu____11481
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11473)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11467 r)
                                            else ();
                                            (lid, uvs2, tps5, c5)))))))))
  
let (tc_polymonadic_bind :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.tscheme ->
            (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env  ->
    fun m  ->
      fun n  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11523 = FStar_Ident.string_of_lid m  in
              let uu____11525 = FStar_Ident.string_of_lid n  in
              let uu____11527 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11523 uu____11525
                uu____11527
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11535 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11535 with
            | (us,t,ty) ->
                let uu____11551 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11551 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11564 =
                         let uu____11569 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11569
                           (fun uu____11586  ->
                              match uu____11586 with
                              | (t1,u) ->
                                  let uu____11597 =
                                    let uu____11598 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11598
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11597, u))
                          in
                       match uu____11564 with
                       | (a,u_a) ->
                           let uu____11606 =
                             let uu____11611 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11611
                               (fun uu____11628  ->
                                  match uu____11628 with
                                  | (t1,u) ->
                                      let uu____11639 =
                                        let uu____11640 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11640
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11639, u))
                              in
                           (match uu____11606 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11657 =
                                    let uu____11658 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11658.FStar_Syntax_Syntax.n  in
                                  match uu____11657 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11670) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11698 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11698 with
                                       | (a',uu____11708)::(b',uu____11710)::bs1
                                           ->
                                           let uu____11740 =
                                             let uu____11741 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11741
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11807 =
                                             let uu____11820 =
                                               let uu____11823 =
                                                 let uu____11824 =
                                                   let uu____11831 =
                                                     let uu____11834 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11834
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11831)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11824
                                                  in
                                               let uu____11847 =
                                                 let uu____11850 =
                                                   let uu____11851 =
                                                     let uu____11858 =
                                                       let uu____11861 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11861
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11858)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11851
                                                    in
                                                 [uu____11850]  in
                                               uu____11823 :: uu____11847  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11820
                                              in
                                           FStar_All.pipe_right uu____11740
                                             uu____11807)
                                  | uu____11882 ->
                                      let uu____11883 =
                                        let uu____11889 =
                                          let uu____11891 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11893 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11891 uu____11893
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11889)
                                         in
                                      FStar_Errors.raise_error uu____11883 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11926 =
                                  let uu____11937 =
                                    let uu____11942 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11943 =
                                      let uu____11944 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11944
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11942 r m u_a uu____11943
                                     in
                                  match uu____11937 with
                                  | (repr,g) ->
                                      let uu____11965 =
                                        let uu____11972 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11972
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11965, g)
                                   in
                                (match uu____11926 with
                                 | (f,guard_f) ->
                                     let uu____12004 =
                                       let x_a =
                                         let uu____12022 =
                                           let uu____12023 =
                                             let uu____12024 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____12024
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____12023
                                            in
                                         FStar_All.pipe_right uu____12022
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____12040 =
                                         let uu____12045 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____12064 =
                                           let uu____12065 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____12065
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____12045 r n u_b uu____12064
                                          in
                                       match uu____12040 with
                                       | (repr,g) ->
                                           let uu____12086 =
                                             let uu____12093 =
                                               let uu____12094 =
                                                 let uu____12095 =
                                                   let uu____12098 =
                                                     let uu____12101 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12101
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12098
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12095
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12094
                                                in
                                             FStar_All.pipe_right uu____12093
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____12086, g)
                                        in
                                     (match uu____12004 with
                                      | (g,guard_g) ->
                                          let uu____12145 =
                                            let uu____12150 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____12151 =
                                              let uu____12152 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____12152
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12150 r p u_b uu____12151
                                             in
                                          (match uu____12145 with
                                           | (repr,guard_repr) ->
                                               let uu____12167 =
                                                 let uu____12172 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____12173 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____12172
                                                   repr uu____12173 r
                                                  in
                                               (match uu____12167 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____12185 =
                                                        let uu____12188 =
                                                          let uu____12189 =
                                                            let uu____12190 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____12190]  in
                                                          let uu____12191 =
                                                            let uu____12202 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____12202]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12189;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12191;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12188
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12185
                                                       in
                                                    let guard_eq =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 ty1 k
                                                       in
                                                    (FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1)
                                                       [guard_f;
                                                       guard_g;
                                                       guard_repr;
                                                       g_pure_wp_uvar;
                                                       guard_eq];
                                                     (let uu____12262 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____12262
                                                      then
                                                        let uu____12266 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____12272 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12266
                                                          uu____12272
                                                      else ());
                                                     (let uu____12282 =
                                                        let uu____12288 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12288)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12282);
                                                     (let uu____12292 =
                                                        let uu____12293 =
                                                          let uu____12296 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12296
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12293)
                                                         in
                                                      ((us1, t), uu____12292)))))))))))
  
let (tc_polymonadic_subcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env0  ->
    fun m  ->
      fun n  ->
        fun ts  ->
          let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
             in
          let combinator_name =
            let uu____12343 = FStar_Ident.string_of_lid m  in
            let uu____12345 =
              let uu____12347 = FStar_Ident.string_of_lid n  in
              Prims.op_Hat "<:" uu____12347  in
            Prims.op_Hat uu____12343 uu____12345  in
          let uu____12350 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts
             in
          match uu____12350 with
          | (us,t,ty) ->
              let uu____12366 = FStar_Syntax_Subst.open_univ_vars us ty  in
              (match uu____12366 with
               | (us1,ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1
                      in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____12379 =
                       let uu____12384 = FStar_Syntax_Util.type_u ()  in
                       FStar_All.pipe_right uu____12384
                         (fun uu____12401  ->
                            match uu____12401 with
                            | (t1,u) ->
                                let uu____12412 =
                                  let uu____12413 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1
                                     in
                                  FStar_All.pipe_right uu____12413
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____12412, u))
                        in
                     match uu____12379 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____12430 =
                             let uu____12431 =
                               FStar_Syntax_Subst.compress ty1  in
                             uu____12431.FStar_Syntax_Syntax.n  in
                           match uu____12430 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____12443)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____12471 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____12471 with
                                | (a',uu____12481)::bs1 ->
                                    let uu____12501 =
                                      let uu____12502 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one))
                                         in
                                      FStar_All.pipe_right uu____12502
                                        FStar_Pervasives_Native.fst
                                       in
                                    let uu____12568 =
                                      let uu____12581 =
                                        let uu____12584 =
                                          let uu____12585 =
                                            let uu____12592 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a)
                                               in
                                            (a', uu____12592)  in
                                          FStar_Syntax_Syntax.NT uu____12585
                                           in
                                        [uu____12584]  in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____12581
                                       in
                                    FStar_All.pipe_right uu____12501
                                      uu____12568)
                           | uu____12607 ->
                               let uu____12608 =
                                 let uu____12614 =
                                   let uu____12616 =
                                     FStar_Syntax_Print.tag_of_term t  in
                                   let uu____12618 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____12616 uu____12618
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____12614)
                                  in
                               FStar_Errors.raise_error uu____12608 r
                            in
                         let bs = a :: rest_bs  in
                         let uu____12645 =
                           let uu____12656 =
                             let uu____12661 =
                               FStar_TypeChecker_Env.push_binders env bs  in
                             let uu____12662 =
                               let uu____12663 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____12663
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____12661 r m u uu____12662
                              in
                           match uu____12656 with
                           | (repr,g) ->
                               let uu____12684 =
                                 let uu____12691 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr
                                    in
                                 FStar_All.pipe_right uu____12691
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               (uu____12684, g)
                            in
                         (match uu____12645 with
                          | (f,guard_f) ->
                              let uu____12723 =
                                let uu____12728 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____12729 =
                                  let uu____12730 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____12730
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____12728 r n u uu____12729
                                 in
                              (match uu____12723 with
                               | (ret_t,guard_ret_t) ->
                                   let uu____12745 =
                                     let uu____12750 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____12751 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name
                                        in
                                     pure_wp_uvar uu____12750 ret_t
                                       uu____12751 r
                                      in
                                   (match uu____12745 with
                                    | (pure_wp_uvar1,guard_wp) ->
                                        let c =
                                          let uu____12761 =
                                            let uu____12762 =
                                              let uu____12763 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              [uu____12763]  in
                                            let uu____12764 =
                                              let uu____12775 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg
                                                 in
                                              [uu____12775]  in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____12762;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____12764;
                                              FStar_Syntax_Syntax.flags = []
                                            }  in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____12761
                                           in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c
                                           in
                                        ((let uu____12830 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc")
                                             in
                                          if uu____12830
                                          then
                                            let uu____12835 =
                                              FStar_Syntax_Print.term_to_string
                                                k
                                               in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____12835
                                          else ());
                                         (let guard_eq =
                                            FStar_TypeChecker_Rel.teq env ty1
                                              k
                                             in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env)
                                            [guard_f;
                                            guard_ret_t;
                                            guard_wp;
                                            guard_eq];
                                          (let k1 =
                                             let uu____12845 =
                                               let uu____12846 =
                                                 FStar_All.pipe_right k
                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____12846
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta;
                                                    FStar_TypeChecker_Env.Eager_unfolding]
                                                    env)
                                                in
                                             FStar_All.pipe_right uu____12845
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us1)
                                              in
                                           (let uu____12850 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc")
                                               in
                                            if uu____12850
                                            then
                                              let uu____12855 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1)
                                                 in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____12855
                                            else ());
                                           ((us1, t), (us1, k1)))))))))))
  