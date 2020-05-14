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
            let uu____752 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____752 with
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
                  let uu____783 =
                    let uu____784 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____784.FStar_Syntax_Syntax.n  in
                  match uu____783 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____787,t,uu____789) ->
                      let uu____814 =
                        let uu____815 = FStar_Syntax_Subst.compress t  in
                        uu____815.FStar_Syntax_Syntax.n  in
                      (match uu____814 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____818,c) ->
                           let uu____840 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____840
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____843 ->
                           let uu____844 =
                             let uu____850 =
                               let uu____852 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____855 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____852 uu____855
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____850)
                              in
                           FStar_Errors.raise_error uu____844 r)
                  | uu____859 ->
                      let uu____860 =
                        let uu____866 =
                          let uu____868 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____871 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____868 uu____871
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____866)  in
                      FStar_Errors.raise_error uu____860 r
                   in
                ((let uu____876 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____882 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____882)
                     in
                  if uu____876
                  then
                    let uu____885 =
                      let uu____891 =
                        let uu____893 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____896 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____893 uu____896
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____891)
                       in
                    FStar_Errors.raise_error uu____885 r
                  else ());
                 (let uu____903 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____903 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____927 = fresh_a_and_u_a "a"  in
                      (match uu____927 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____953 = signature  in
                               match uu____953 with
                               | (us1,t,uu____968) -> (us1, t)  in
                             let uu____985 =
                               let uu____986 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____986
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____985
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1013 =
                               let uu____1016 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1016
                                 (fun uu____1029  ->
                                    match uu____1029 with
                                    | (t,u1) ->
                                        let uu____1036 =
                                          let uu____1039 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1039
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1036)
                                in
                             FStar_Syntax_Util.arrow bs uu____1013  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1042 =
                               let uu____1055 =
                                 let uu____1058 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1058
                                  in
                               (repr_us, repr_t, uu____1055)  in
                             (uu____1042, underlying_effect_lid))))))
             in
          match uu____718 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1131 = signature  in
                    match uu____1131 with | (us,t,uu____1146) -> (us, t)  in
                  let repr_ts =
                    let uu____1164 = repr  in
                    match uu____1164 with | (us,t,uu____1179) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n t r =
                  let uu____1229 =
                    let uu____1235 =
                      let uu____1237 =
                        FStar_Ident.string_of_lid
                          ed.FStar_Syntax_Syntax.mname
                         in
                      let uu____1239 = FStar_Util.string_of_int n  in
                      let uu____1241 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1243 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        uu____1237 comb uu____1239 uu____1241 uu____1243
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1235)  in
                  FStar_Errors.raise_error uu____1229 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1273 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1273 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1301 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1301 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1325 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1325 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1346 = fresh_a_and_u_a "a"  in
                             match uu____1346 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1377 =
                                     let uu____1378 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1378.FStar_Syntax_Syntax.n  in
                                   match uu____1377 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1390) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1418 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1418 with
                                        | (a',uu____1428)::(x',uu____1430)::bs1
                                            ->
                                            let uu____1460 =
                                              let uu____1461 =
                                                let uu____1466 =
                                                  let uu____1469 =
                                                    let uu____1470 =
                                                      let uu____1477 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1477)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1470
                                                     in
                                                  [uu____1469]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1466
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1461
                                               in
                                            let uu____1484 =
                                              let uu____1497 =
                                                let uu____1500 =
                                                  let uu____1501 =
                                                    let uu____1508 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1508)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1501
                                                   in
                                                [uu____1500]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1497
                                               in
                                            FStar_All.pipe_right uu____1460
                                              uu____1484)
                                   | uu____1523 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1547 =
                                   let uu____1552 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1553 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1552 u_a uu____1553  in
                                 (match uu____1547 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1573 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1573
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1578 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1578);
                                       (let uu____1579 =
                                          let uu____1582 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1582
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1579)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1611 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1611 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1623 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1623 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1647 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1647 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1668 = fresh_a_and_u_a "a"  in
                              match uu____1668 with
                              | (a,u_a) ->
                                  let uu____1688 = fresh_a_and_u_a "b"  in
                                  (match uu____1688 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1717 =
                                           let uu____1718 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1718.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1717 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1730) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1758 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1758 with
                                              | (a',uu____1768)::(b',uu____1770)::bs1
                                                  ->
                                                  let uu____1800 =
                                                    let uu____1801 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1801
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1867 =
                                                    let uu____1880 =
                                                      let uu____1883 =
                                                        let uu____1884 =
                                                          let uu____1891 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1891)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1884
                                                         in
                                                      let uu____1898 =
                                                        let uu____1901 =
                                                          let uu____1902 =
                                                            let uu____1909 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1909)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1902
                                                           in
                                                        [uu____1901]  in
                                                      uu____1883 ::
                                                        uu____1898
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1880
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1800 uu____1867)
                                         | uu____1924 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1948 =
                                         let uu____1959 =
                                           let uu____1964 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1965 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1964 u_a
                                             uu____1965
                                            in
                                         match uu____1959 with
                                         | (repr1,g) ->
                                             let uu____1980 =
                                               let uu____1987 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____1987
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____1980, g)
                                          in
                                       (match uu____1948 with
                                        | (f,guard_f) ->
                                            let uu____2027 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2040 =
                                                let uu____2045 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2064 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2045 u_b
                                                  uu____2064
                                                 in
                                              match uu____2040 with
                                              | (repr1,g) ->
                                                  let uu____2079 =
                                                    let uu____2086 =
                                                      let uu____2087 =
                                                        let uu____2088 =
                                                          let uu____2091 =
                                                            let uu____2094 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2094
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2091
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2088
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2087
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2086
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2079, g)
                                               in
                                            (match uu____2027 with
                                             | (g,guard_g) ->
                                                 let uu____2146 =
                                                   let uu____2151 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2152 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2151
                                                     u_b uu____2152
                                                    in
                                                 (match uu____2146 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2169 =
                                                        let uu____2174 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2175 =
                                                          let uu____2177 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname
                                                             in
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            uu____2177
                                                           in
                                                        pure_wp_uvar
                                                          uu____2174 repr1
                                                          uu____2175 r
                                                         in
                                                      (match uu____2169 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2197 =
                                                               let uu____2200
                                                                 =
                                                                 let uu____2201
                                                                   =
                                                                   let uu____2202
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2202]
                                                                    in
                                                                 let uu____2203
                                                                   =
                                                                   let uu____2214
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2214]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2201;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2203;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2200
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2197
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
                                                            (let uu____2273 =
                                                               let uu____2276
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2276
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2273)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2305 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2305 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2317 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2317 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2342 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc")
                             in
                          if uu____2342
                          then
                            let uu____2347 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2353 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2347 uu____2353
                          else ());
                         (let uu____2362 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2362 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2383 = fresh_a_and_u_a "a"  in
                                match uu____2383 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2412 =
                                        let uu____2413 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2413.FStar_Syntax_Syntax.n  in
                                      match uu____2412 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2425) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2453 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2453 with
                                           | (a',uu____2463)::bs1 ->
                                               let uu____2483 =
                                                 let uu____2484 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2484
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2582 =
                                                 let uu____2595 =
                                                   let uu____2598 =
                                                     let uu____2599 =
                                                       let uu____2606 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2606)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2599
                                                      in
                                                   [uu____2598]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2595
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2483 uu____2582)
                                      | uu____2621 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2639 =
                                      let uu____2650 =
                                        let uu____2655 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2656 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2655 u uu____2656
                                         in
                                      match uu____2650 with
                                      | (repr1,g) ->
                                          let uu____2671 =
                                            let uu____2678 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2678
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2671, g)
                                       in
                                    (match uu____2639 with
                                     | (f,guard_f) ->
                                         let uu____2718 =
                                           let uu____2723 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2724 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2723 u
                                             uu____2724
                                            in
                                         (match uu____2718 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2741 =
                                                let uu____2746 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2747 =
                                                  let uu____2749 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    uu____2749
                                                   in
                                                pure_wp_uvar uu____2746 ret_t
                                                  uu____2747 r
                                                 in
                                              (match uu____2741 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2767 =
                                                       let uu____2768 =
                                                         let uu____2769 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2769]  in
                                                       let uu____2770 =
                                                         let uu____2781 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2781]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2768;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2770;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2767
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2836 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffectsTc")
                                                        in
                                                     if uu____2836
                                                     then
                                                       let uu____2841 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type of subcomp before unification: %s\n"
                                                         uu____2841
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
                                                     (let uu____2848 =
                                                        let uu____2851 =
                                                          let uu____2852 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2852
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2851
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2848)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else =
                     let if_then_else_ts =
                       let uu____2881 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2881 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2909 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2909 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2933 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2933 with
                          | (us,t) ->
                              let uu____2952 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2952 with
                               | (uu____2969,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____2973 = fresh_a_and_u_a "a"  in
                                     match uu____2973 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3002 =
                                             let uu____3003 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3003.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3002 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3015) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3043 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3043 with
                                                | (a',uu____3053)::bs1 ->
                                                    let uu____3073 =
                                                      let uu____3074 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3074
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3172 =
                                                      let uu____3185 =
                                                        let uu____3188 =
                                                          let uu____3189 =
                                                            let uu____3196 =
                                                              let uu____3199
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3199
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3196)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3189
                                                           in
                                                        [uu____3188]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3185
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3073 uu____3172)
                                           | uu____3220 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3238 =
                                           let uu____3249 =
                                             let uu____3254 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3255 =
                                               let uu____3256 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3256
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3254 u_a
                                               uu____3255
                                              in
                                           match uu____3249 with
                                           | (repr1,g) ->
                                               let uu____3277 =
                                                 let uu____3284 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3284
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3277, g)
                                            in
                                         (match uu____3238 with
                                          | (f_bs,guard_f) ->
                                              let uu____3324 =
                                                let uu____3335 =
                                                  let uu____3340 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3341 =
                                                    let uu____3342 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3342
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3340 u_a
                                                    uu____3341
                                                   in
                                                match uu____3335 with
                                                | (repr1,g) ->
                                                    let uu____3363 =
                                                      let uu____3370 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3370
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3363, g)
                                                 in
                                              (match uu____3324 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3417 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3417
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3425 =
                                                     let uu____3430 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3449 =
                                                       let uu____3450 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3450
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3430
                                                       u_a uu____3449
                                                      in
                                                   (match uu____3425 with
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
                                                         (let uu____3510 =
                                                            let uu____3513 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3513
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3510,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else;
                   (let r =
                      let uu____3526 =
                        let uu____3529 =
                          let uu____3538 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3538 FStar_Util.must  in
                        FStar_All.pipe_right uu____3529
                          FStar_Pervasives_Native.snd
                         in
                      uu____3526.FStar_Syntax_Syntax.pos  in
                    let uu____3567 = if_then_else  in
                    match uu____3567 with
                    | (ite_us,ite_t,uu____3582) ->
                        let uu____3595 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3595 with
                         | (us,ite_t1) ->
                             let uu____3602 =
                               let uu____3617 =
                                 let uu____3618 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3618.FStar_Syntax_Syntax.n  in
                               match uu____3617 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3636,uu____3637) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3663 =
                                     let uu____3676 =
                                       let uu____3681 =
                                         let uu____3684 =
                                           let uu____3693 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3693
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3684
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3681
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3676
                                       (fun l  ->
                                          let uu____3849 = l  in
                                          match uu____3849 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3663 with
                                    | (f,g,p) ->
                                        let uu____3918 =
                                          let uu____3919 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3919 bs1
                                           in
                                        let uu____3920 =
                                          let uu____3921 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.map
                                                 (fun uu____3946  ->
                                                    match uu____3946 with
                                                    | (b,qual) ->
                                                        let uu____3965 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            b
                                                           in
                                                        (uu____3965, qual)))
                                             in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            ite_t1 uu____3921 r
                                           in
                                        (uu____3918, uu____3920, f, g, p))
                               | uu____3972 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3602 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____4001 =
                                    let uu____4010 = stronger_repr  in
                                    match uu____4010 with
                                    | (uu____4031,subcomp_t,subcomp_ty) ->
                                        let uu____4046 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____4046 with
                                         | (uu____4059,subcomp_t1) ->
                                             let uu____4061 =
                                               let uu____4072 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____4072 with
                                               | (uu____4087,subcomp_ty1) ->
                                                   let uu____4089 =
                                                     let uu____4090 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____4090.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____4089 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4104) ->
                                                        let uu____4125 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        (match uu____4125
                                                         with
                                                         | (bs_except_last,last_b)
                                                             ->
                                                             let uu____4231 =
                                                               FStar_All.pipe_right
                                                                 bs_except_last
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             let uu____4258 =
                                                               let uu____4261
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   last_b
                                                                   FStar_List.hd
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____4261
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             (uu____4231,
                                                               uu____4258))
                                                    | uu____4304 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             (match uu____4061 with
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
                                                  let uu____4415 = aux f_t
                                                     in
                                                  let uu____4418 = aux g_t
                                                     in
                                                  (uu____4415, uu____4418)))
                                     in
                                  (match uu____4001 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4435 =
                                         let aux t =
                                           let uu____4452 =
                                             let uu____4453 =
                                               let uu____4480 =
                                                 let uu____4497 =
                                                   let uu____4506 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       ite_t_applied
                                                      in
                                                   FStar_Util.Inr uu____4506
                                                    in
                                                 (uu____4497,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               (t, uu____4480,
                                                 FStar_Pervasives_Native.None)
                                                in
                                             FStar_Syntax_Syntax.Tm_ascribed
                                               uu____4453
                                              in
                                           FStar_Syntax_Syntax.mk uu____4452
                                             r
                                            in
                                         let uu____4547 = aux subcomp_f  in
                                         let uu____4548 = aux subcomp_g  in
                                         (uu____4547, uu____4548)  in
                                       (match uu____4435 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4552 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc")
                                                 in
                                              if uu____4552
                                              then
                                                let uu____4557 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4559 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4557 uu____4559
                                              else ());
                                             (let uu____4564 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4564 with
                                              | (uu____4571,uu____4572,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4575 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4575 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4577 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4577 with
                                                    | (uu____4584,uu____4585,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4589 =
                                                              let uu____4590
                                                                =
                                                                FStar_Syntax_Syntax.lid_as_fv
                                                                  FStar_Parser_Const.not_lid
                                                                  FStar_Syntax_Syntax.delta_constant
                                                                  FStar_Pervasives_Native.None
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____4590
                                                                FStar_Syntax_Syntax.fv_to_tm
                                                               in
                                                            let uu____4591 =
                                                              let uu____4592
                                                                =
                                                                FStar_All.pipe_right
                                                                  p_t
                                                                  FStar_Syntax_Syntax.as_arg
                                                                 in
                                                              [uu____4592]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              uu____4589
                                                              uu____4591 r
                                                             in
                                                          let uu____4625 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4625 g_g
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
                        (let uu____4649 =
                           let uu____4655 =
                             let uu____4657 =
                               FStar_Ident.string_of_lid
                                 ed.FStar_Syntax_Syntax.mname
                                in
                             let uu____4659 =
                               FStar_Ident.string_of_lid
                                 act.FStar_Syntax_Syntax.action_name
                                in
                             let uu____4661 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               uu____4657 uu____4659 uu____4661
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4655)
                            in
                         FStar_Errors.raise_error uu____4649 r)
                      else ();
                      (let uu____4668 =
                         let uu____4673 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4673 with
                         | (usubst,us) ->
                             let uu____4696 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4697 =
                               let uu___455_4698 = act  in
                               let uu____4699 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4700 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___455_4698.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___455_4698.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___455_4698.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4699;
                                 FStar_Syntax_Syntax.action_typ = uu____4700
                               }  in
                             (uu____4696, uu____4697)
                          in
                       match uu____4668 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4704 =
                               let uu____4705 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4705.FStar_Syntax_Syntax.n  in
                             match uu____4704 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4731 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4731
                                 then
                                   let repr_ts =
                                     let uu____4735 = repr  in
                                     match uu____4735 with
                                     | (us,t,uu____4750) -> (us, t)  in
                                   let repr1 =
                                     let uu____4768 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4768
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4778 =
                                       let uu____4779 =
                                         FStar_Syntax_Syntax.as_arg
                                           ct.FStar_Syntax_Syntax.result_typ
                                          in
                                       uu____4779 ::
                                         (ct.FStar_Syntax_Syntax.effect_args)
                                        in
                                     FStar_Syntax_Syntax.mk_Tm_app repr1
                                       uu____4778 r
                                      in
                                   let c1 =
                                     let uu____4797 =
                                       let uu____4800 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4800
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4797
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4803 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4804 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4804 with
                            | (act_typ1,uu____4812,g_t) ->
                                let uu____4814 =
                                  let uu____4821 =
                                    let uu___480_4822 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___480_4822.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___480_4822.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___480_4822.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___480_4822.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___480_4822.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___480_4822.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___480_4822.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___480_4822.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___480_4822.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___480_4822.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___480_4822.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___480_4822.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___480_4822.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___480_4822.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___480_4822.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___480_4822.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___480_4822.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___480_4822.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___480_4822.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___480_4822.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___480_4822.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___480_4822.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___480_4822.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___480_4822.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___480_4822.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___480_4822.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___480_4822.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___480_4822.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___480_4822.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___480_4822.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___480_4822.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___480_4822.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___480_4822.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___480_4822.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___480_4822.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___480_4822.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___480_4822.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___480_4822.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___480_4822.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___480_4822.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___480_4822.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___480_4822.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___480_4822.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___480_4822.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___480_4822.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___480_4822.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4821
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4814 with
                                 | (act_defn,uu____4825,g_d) ->
                                     ((let uu____4828 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffectsTc")
                                          in
                                       if uu____4828
                                       then
                                         let uu____4833 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4835 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4833 uu____4835
                                       else ());
                                      (let uu____4840 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4848 =
                                           let uu____4849 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4849.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4848 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4859) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4882 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4882 with
                                              | (t,u) ->
                                                  let reason =
                                                    let uu____4897 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname
                                                       in
                                                    let uu____4899 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name
                                                       in
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      uu____4897 uu____4899
                                                     in
                                                  let uu____4902 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4902 with
                                                   | (a_tm,uu____4922,g_tm)
                                                       ->
                                                       let uu____4936 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4936 with
                                                        | (repr1,g) ->
                                                            let uu____4949 =
                                                              let uu____4952
                                                                =
                                                                let uu____4955
                                                                  =
                                                                  let uu____4958
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4958
                                                                    (
                                                                    fun
                                                                    uu____4961
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____4961)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4955
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4952
                                                               in
                                                            let uu____4962 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4949,
                                                              uu____4962))))
                                         | uu____4965 ->
                                             let uu____4966 =
                                               let uu____4972 =
                                                 let uu____4974 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname
                                                    in
                                                 let uu____4976 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name
                                                    in
                                                 let uu____4978 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   uu____4974 uu____4976
                                                   uu____4978
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4972)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4966 r
                                          in
                                       match uu____4840 with
                                       | (k,g_k) ->
                                           ((let uu____4995 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffectsTc")
                                                in
                                             if uu____4995
                                             then
                                               let uu____5000 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____5000
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____5008 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc")
                                                 in
                                              if uu____5008
                                              then
                                                let uu____5013 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____5013
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____5026 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  let uu____5028 =
                                                    FStar_Ident.string_of_lid
                                                      act1.FStar_Syntax_Syntax.action_name
                                                     in
                                                  let uu____5030 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    uu____5026 uu____5028
                                                    uu____5030
                                                   in
                                                let repr_args t =
                                                  let uu____5051 =
                                                    let uu____5052 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5052.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5051 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,a::is) ->
                                                      let uu____5104 =
                                                        let uu____5105 =
                                                          FStar_Syntax_Subst.compress
                                                            head
                                                           in
                                                        uu____5105.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____5104 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____5114,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____5124 ->
                                                           let uu____5125 =
                                                             let uu____5131 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____5131)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5125 r)
                                                  | uu____5140 ->
                                                      let uu____5141 =
                                                        let uu____5147 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5147)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____5141 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____5157 =
                                                  let uu____5158 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____5158.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5157 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____5183 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____5183 with
                                                     | (bs1,c1) ->
                                                         let uu____5190 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____5190
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
                                                              let uu____5201
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5201))
                                                | uu____5204 ->
                                                    let uu____5205 =
                                                      let uu____5211 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____5211)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____5205 r
                                                 in
                                              (let uu____5215 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffectsTc")
                                                  in
                                               if uu____5215
                                               then
                                                 let uu____5220 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5220
                                               else ());
                                              (let act2 =
                                                 let uu____5226 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5226 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___553_5240 =
                                                         act1  in
                                                       let uu____5241 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___553_5240.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___553_5240.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___553_5240.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5241
                                                       }
                                                     else
                                                       (let uu____5244 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5251
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5251
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5244
                                                        then
                                                          let uu___558_5256 =
                                                            act1  in
                                                          let uu____5257 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___558_5256.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___558_5256.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___558_5256.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___558_5256.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5257
                                                          }
                                                        else
                                                          (let uu____5260 =
                                                             let uu____5266 =
                                                               let uu____5268
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   ed.FStar_Syntax_Syntax.mname
                                                                  in
                                                               let uu____5270
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   act1.FStar_Syntax_Syntax.action_name
                                                                  in
                                                               let uu____5272
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5274
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 uu____5268
                                                                 uu____5270
                                                                 uu____5272
                                                                 uu____5274
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5266)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5260 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5299 =
                      match uu____5299 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5344 =
                        let uu____5345 = tschemes_of repr  in
                        let uu____5350 = tschemes_of return_repr  in
                        let uu____5355 = tschemes_of bind_repr  in
                        let uu____5360 = tschemes_of stronger_repr  in
                        let uu____5365 = tschemes_of if_then_else  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5345;
                          FStar_Syntax_Syntax.l_return = uu____5350;
                          FStar_Syntax_Syntax.l_bind = uu____5355;
                          FStar_Syntax_Syntax.l_subcomp = uu____5360;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5365
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5344  in
                    let uu___567_5370 = ed  in
                    let uu____5371 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___567_5370.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___567_5370.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___567_5370.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___567_5370.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5378 = signature  in
                         match uu____5378 with | (us,t,uu____5393) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5371;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___567_5370.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5431 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5431
         then
           let uu____5436 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5436
         else ());
        (let uu____5442 =
           let uu____5447 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5447 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5471 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5471  in
               let uu____5472 =
                 let uu____5479 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5479 bs  in
               (match uu____5472 with
                | (bs1,uu____5485,uu____5486) ->
                    let uu____5487 =
                      let tmp_t =
                        let uu____5497 =
                          let uu____5500 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5505  ->
                                 FStar_Pervasives_Native.Some uu____5505)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5500
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5497  in
                      let uu____5506 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5506 with
                      | (us,tmp_t1) ->
                          let uu____5523 =
                            let uu____5524 =
                              let uu____5525 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5525
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5524
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5523)
                       in
                    (match uu____5487 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5562 ->
                              let uu____5565 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5572 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5572 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5565
                              then (us, bs2)
                              else
                                (let uu____5583 =
                                   let uu____5589 =
                                     let uu____5591 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname
                                        in
                                     let uu____5593 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5595 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5591 uu____5593 uu____5595
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5589)
                                    in
                                 let uu____5599 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5583
                                   uu____5599))))
            in
         match uu____5442 with
         | (us,bs) ->
             let ed1 =
               let uu___601_5607 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___601_5607.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___601_5607.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___601_5607.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___601_5607.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___601_5607.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___601_5607.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5608 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5608 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5627 =
                    let uu____5632 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5632  in
                  (match uu____5627 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5653 =
                           match uu____5653 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5673 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5673 t  in
                               let uu____5682 =
                                 let uu____5683 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5683 t1  in
                               (us1, uu____5682)
                            in
                         let uu___615_5688 = ed1  in
                         let uu____5689 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5690 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5691 =
                           FStar_List.map
                             (fun a  ->
                                let uu___618_5699 = a  in
                                let uu____5700 =
                                  let uu____5701 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5701  in
                                let uu____5712 =
                                  let uu____5713 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5713  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___618_5699.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___618_5699.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___618_5699.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___618_5699.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5700;
                                  FStar_Syntax_Syntax.action_typ = uu____5712
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___615_5688.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___615_5688.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___615_5688.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___615_5688.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5689;
                           FStar_Syntax_Syntax.combinators = uu____5690;
                           FStar_Syntax_Syntax.actions = uu____5691;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___615_5688.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5725 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5725
                         then
                           let uu____5730 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5730
                         else ());
                        (let env =
                           let uu____5737 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5737
                             ed_bs
                            in
                         let check_and_gen' comb n env_opt uu____5772 k =
                           match uu____5772 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5792 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5792 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5801 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5801 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5802 =
                                            let uu____5809 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5809 t1
                                             in
                                          (match uu____5802 with
                                           | (t2,uu____5811,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5814 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5814 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5830 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname
                                                  in
                                               let uu____5832 =
                                                 FStar_Util.string_of_int n
                                                  in
                                               let uu____5834 =
                                                 let uu____5836 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5836
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5830 comb uu____5832
                                                 uu____5834
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5851 ->
                                               let uu____5852 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5859 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5859 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5852
                                               then (g_us, t3)
                                               else
                                                 (let uu____5870 =
                                                    let uu____5876 =
                                                      let uu____5878 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      let uu____5880 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5882 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5878 comb
                                                        uu____5880 uu____5882
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5876)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5870
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5890 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5890
                          then
                            let uu____5895 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5895
                          else ());
                         (let fresh_a_and_wp uu____5911 =
                            let fail t =
                              let uu____5924 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5924
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5940 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5940 with
                            | (uu____5951,signature1) ->
                                let uu____5953 =
                                  let uu____5954 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5954.FStar_Syntax_Syntax.n  in
                                (match uu____5953 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5964) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5993)::(wp,uu____5995)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6024 -> fail signature1)
                                 | uu____6025 -> fail signature1)
                             in
                          let log_combinator s ts =
                            let uu____6039 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____6039
                            then
                              let uu____6044 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname
                                 in
                              let uu____6046 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____6044 s uu____6046
                            else ()  in
                          let ret_wp =
                            let uu____6052 = fresh_a_and_wp ()  in
                            match uu____6052 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____6068 =
                                    let uu____6077 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____6084 =
                                      let uu____6093 =
                                        let uu____6100 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6100
                                         in
                                      [uu____6093]  in
                                    uu____6077 :: uu____6084  in
                                  let uu____6119 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____6068
                                    uu____6119
                                   in
                                let uu____6122 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6122
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6136 = fresh_a_and_wp ()  in
                             match uu____6136 with
                             | (a,wp_sort_a) ->
                                 let uu____6149 = fresh_a_and_wp ()  in
                                 (match uu____6149 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6165 =
                                          let uu____6174 =
                                            let uu____6181 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6181
                                             in
                                          [uu____6174]  in
                                        let uu____6194 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6165
                                          uu____6194
                                         in
                                      let k =
                                        let uu____6200 =
                                          let uu____6209 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6216 =
                                            let uu____6225 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6232 =
                                              let uu____6241 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6248 =
                                                let uu____6257 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6264 =
                                                  let uu____6273 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6273]  in
                                                uu____6257 :: uu____6264  in
                                              uu____6241 :: uu____6248  in
                                            uu____6225 :: uu____6232  in
                                          uu____6209 :: uu____6216  in
                                        let uu____6316 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6200
                                          uu____6316
                                         in
                                      let uu____6319 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6319
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6333 = fresh_a_and_wp ()  in
                              match uu____6333 with
                              | (a,wp_sort_a) ->
                                  let uu____6346 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6346 with
                                   | (t,uu____6352) ->
                                       let k =
                                         let uu____6356 =
                                           let uu____6365 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6372 =
                                             let uu____6381 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6388 =
                                               let uu____6397 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6397]  in
                                             uu____6381 :: uu____6388  in
                                           uu____6365 :: uu____6372  in
                                         let uu____6428 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6356
                                           uu____6428
                                          in
                                       let uu____6431 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6431
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6445 = fresh_a_and_wp ()  in
                               match uu____6445 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6459 =
                                       let uu____6462 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6462
                                        in
                                     let uu____6463 =
                                       let uu____6464 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6464
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6459
                                       uu____6463
                                      in
                                   let k =
                                     let uu____6476 =
                                       let uu____6485 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6492 =
                                         let uu____6501 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6508 =
                                           let uu____6517 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6524 =
                                             let uu____6533 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6533]  in
                                           uu____6517 :: uu____6524  in
                                         uu____6501 :: uu____6508  in
                                       uu____6485 :: uu____6492  in
                                     let uu____6570 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6476
                                       uu____6570
                                      in
                                   let uu____6573 =
                                     let uu____6578 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6578
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6573
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6610 = fresh_a_and_wp ()  in
                                match uu____6610 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6626 =
                                        let uu____6635 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6642 =
                                          let uu____6651 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6651]  in
                                        uu____6635 :: uu____6642  in
                                      let uu____6676 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6626
                                        uu____6676
                                       in
                                    let uu____6679 =
                                      let uu____6684 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6684
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6679
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6700 = fresh_a_and_wp ()  in
                                 match uu____6700 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6714 =
                                         let uu____6717 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6717
                                          in
                                       let uu____6718 =
                                         let uu____6719 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6719
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6714
                                         uu____6718
                                        in
                                     let wp_sort_b_a =
                                       let uu____6731 =
                                         let uu____6740 =
                                           let uu____6747 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6747
                                            in
                                         [uu____6740]  in
                                       let uu____6760 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6731
                                         uu____6760
                                        in
                                     let k =
                                       let uu____6766 =
                                         let uu____6775 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6782 =
                                           let uu____6791 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6798 =
                                             let uu____6807 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6807]  in
                                           uu____6791 :: uu____6798  in
                                         uu____6775 :: uu____6782  in
                                       let uu____6838 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6766
                                         uu____6838
                                        in
                                     let uu____6841 =
                                       let uu____6846 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6846
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6841
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6862 = fresh_a_and_wp ()  in
                                  match uu____6862 with
                                  | (a,wp_sort_a) ->
                                      let uu____6875 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6875 with
                                       | (t,uu____6881) ->
                                           let k =
                                             let uu____6885 =
                                               let uu____6894 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6901 =
                                                 let uu____6910 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6910]  in
                                               uu____6894 :: uu____6901  in
                                             let uu____6935 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6885 uu____6935
                                              in
                                           let trivial =
                                             let uu____6939 =
                                               let uu____6944 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6944 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6939
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6959 =
                                  let uu____6976 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6976 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____7005 ->
                                      let repr =
                                        let uu____7009 = fresh_a_and_wp ()
                                           in
                                        match uu____7009 with
                                        | (a,wp_sort_a) ->
                                            let uu____7022 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____7022 with
                                             | (t,uu____7028) ->
                                                 let k =
                                                   let uu____7032 =
                                                     let uu____7041 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____7048 =
                                                       let uu____7057 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____7057]  in
                                                     uu____7041 :: uu____7048
                                                      in
                                                   let uu____7082 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7032 uu____7082
                                                    in
                                                 let uu____7085 =
                                                   let uu____7090 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7090
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7085
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7134 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____7134 with
                                          | (uu____7141,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____7144 =
                                                let uu____7145 =
                                                  let uu____7162 =
                                                    let uu____7173 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7190 =
                                                      let uu____7201 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7201]  in
                                                    uu____7173 :: uu____7190
                                                     in
                                                  (repr2, uu____7162)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____7145
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7144
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7267 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7267 wp  in
                                        let destruct_repr t =
                                          let uu____7282 =
                                            let uu____7283 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7283.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7282 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7294,(t1,uu____7296)::
                                               (wp,uu____7298)::[])
                                              -> (t1, wp)
                                          | uu____7357 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7373 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7373
                                              FStar_Util.must
                                             in
                                          let uu____7400 = fresh_a_and_wp ()
                                             in
                                          match uu____7400 with
                                          | (a,uu____7408) ->
                                              let x_a =
                                                let uu____7414 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7414
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7420 =
                                                    let uu____7421 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7421
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____7430 =
                                                    let uu____7431 =
                                                      let uu____7440 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7440
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7449 =
                                                      let uu____7460 =
                                                        let uu____7469 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7469
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7460]  in
                                                    uu____7431 :: uu____7449
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7420 uu____7430
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7505 =
                                                  let uu____7514 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7521 =
                                                    let uu____7530 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7530]  in
                                                  uu____7514 :: uu____7521
                                                   in
                                                let uu____7555 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7505 uu____7555
                                                 in
                                              let uu____7558 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7558 with
                                               | (k1,uu____7566,uu____7567)
                                                   ->
                                                   let env1 =
                                                     let uu____7571 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7571
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
                                             let uu____7584 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7584
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7622 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7622
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7623 = fresh_a_and_wp ()
                                              in
                                           match uu____7623 with
                                           | (a,wp_sort_a) ->
                                               let uu____7636 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7636 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7652 =
                                                        let uu____7661 =
                                                          let uu____7668 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7668
                                                           in
                                                        [uu____7661]  in
                                                      let uu____7681 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7652 uu____7681
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
                                                      let uu____7689 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7689
                                                       in
                                                    let wp_g_x =
                                                      let uu____7692 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g
                                                         in
                                                      let uu____7693 =
                                                        let uu____7694 =
                                                          let uu____7703 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7703
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7694]  in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7692 uu____7693
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7732 =
                                                          let uu____7733 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7733
                                                            FStar_Pervasives_Native.snd
                                                           in
                                                        let uu____7742 =
                                                          let uu____7743 =
                                                            let uu____7746 =
                                                              let uu____7749
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a
                                                                 in
                                                              let uu____7750
                                                                =
                                                                let uu____7753
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b
                                                                   in
                                                                let uu____7754
                                                                  =
                                                                  let uu____7757
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  let uu____7758
                                                                    =
                                                                    let uu____7761
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7761]
                                                                     in
                                                                  uu____7757
                                                                    ::
                                                                    uu____7758
                                                                   in
                                                                uu____7753 ::
                                                                  uu____7754
                                                                 in
                                                              uu____7749 ::
                                                                uu____7750
                                                               in
                                                            r :: uu____7746
                                                             in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7743
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7732
                                                          uu____7742
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7779 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7779
                                                      then
                                                        let uu____7790 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7797 =
                                                          let uu____7806 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7806]  in
                                                        uu____7790 ::
                                                          uu____7797
                                                      else []  in
                                                    let k =
                                                      let uu____7842 =
                                                        let uu____7851 =
                                                          let uu____7860 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7867 =
                                                            let uu____7876 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7876]  in
                                                          uu____7860 ::
                                                            uu____7867
                                                           in
                                                        let uu____7901 =
                                                          let uu____7910 =
                                                            let uu____7919 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7926 =
                                                              let uu____7935
                                                                =
                                                                let uu____7942
                                                                  =
                                                                  let uu____7943
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7943
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7942
                                                                 in
                                                              let uu____7944
                                                                =
                                                                let uu____7953
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7960
                                                                  =
                                                                  let uu____7969
                                                                    =
                                                                    let uu____7976
                                                                    =
                                                                    let uu____7977
                                                                    =
                                                                    let uu____7986
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7986]
                                                                     in
                                                                    let uu____8005
                                                                    =
                                                                    let uu____8008
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____8008
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7977
                                                                    uu____8005
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7976
                                                                     in
                                                                  [uu____7969]
                                                                   in
                                                                uu____7953 ::
                                                                  uu____7960
                                                                 in
                                                              uu____7935 ::
                                                                uu____7944
                                                               in
                                                            uu____7919 ::
                                                              uu____7926
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7910
                                                           in
                                                        FStar_List.append
                                                          uu____7851
                                                          uu____7901
                                                         in
                                                      let uu____8053 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7842 uu____8053
                                                       in
                                                    let uu____8056 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____8056 with
                                                     | (k1,uu____8064,uu____8065)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___813_8075
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___813_8075.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____8077 
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8077)
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
                                              (let uu____8104 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8118 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____8118 with
                                                    | (usubst,uvs) ->
                                                        let uu____8141 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____8142 =
                                                          let uu___826_8143 =
                                                            act  in
                                                          let uu____8144 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____8145 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___826_8143.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___826_8143.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___826_8143.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8144;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8145
                                                          }  in
                                                        (uu____8141,
                                                          uu____8142))
                                                  in
                                               match uu____8104 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____8149 =
                                                       let uu____8150 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____8150.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____8149 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____8176 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____8176
                                                         then
                                                           let uu____8179 =
                                                             let uu____8182 =
                                                               let uu____8183
                                                                 =
                                                                 let uu____8184
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8184
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8183
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8182
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8179
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8207 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8208 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8208 with
                                                    | (act_typ1,uu____8216,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___843_8219 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___843_8219.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          }  in
                                                        ((let uu____8222 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8222
                                                          then
                                                            let uu____8226 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8228 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8230 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8226
                                                              uu____8228
                                                              uu____8230
                                                          else ());
                                                         (let uu____8235 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8235
                                                          with
                                                          | (act_defn,uu____8243,g_a)
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
                                                              let uu____8247
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
                                                                    let uu____8283
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8283
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8295)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8302
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8302
                                                                     in
                                                                    let uu____8305
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8305
                                                                    with
                                                                    | 
                                                                    (k1,uu____8319,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8323
                                                                    ->
                                                                    let uu____8324
                                                                    =
                                                                    let uu____8330
                                                                    =
                                                                    let uu____8332
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8334
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8332
                                                                    uu____8334
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8330)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8324
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8247
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
                                                                    let uu____8352
                                                                    =
                                                                    let uu____8353
                                                                    =
                                                                    let uu____8354
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8354
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8353
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8352);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8356
                                                                    =
                                                                    let uu____8357
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8357.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8356
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8382
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8382
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8389
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8389
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8409
                                                                    =
                                                                    let uu____8410
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8410]
                                                                     in
                                                                    let uu____8411
                                                                    =
                                                                    let uu____8422
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8422]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8409;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8411;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8447
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8447))
                                                                    | 
                                                                    uu____8450
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8452
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8474
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8474))
                                                                     in
                                                                    match uu____8452
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
                                                                    let uu___893_8493
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___893_8493.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___893_8493.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___893_8493.FStar_Syntax_Syntax.action_params);
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
                                match uu____6959 with
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
                                      let uu____8536 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8536 ts1
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
                                          uu____8548 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8549 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8550 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___913_8553 = ed2  in
                                      let uu____8554 = cl signature  in
                                      let uu____8555 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___916_8563 = a  in
                                             let uu____8564 =
                                               let uu____8565 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8565
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8590 =
                                               let uu____8591 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8591
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___916_8563.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___916_8563.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___916_8563.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___916_8563.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8564;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8590
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___913_8553.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___913_8553.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___913_8553.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___913_8553.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8554;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8555;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___913_8553.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8617 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8617
                                      then
                                        let uu____8622 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8622
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
        let uu____8648 =
          let uu____8663 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8663 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8648 env ed quals
  
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
        let fail uu____8713 =
          let uu____8714 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8720 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8714 uu____8720  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8764)::(wp,uu____8766)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8795 -> fail ())
        | uu____8796 -> fail ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub  ->
      (let uu____8809 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc")
          in
       if uu____8809
       then
         let uu____8814 = FStar_Syntax_Print.sub_eff_to_string sub  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8814
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8831 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8831.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.target
           in
        let uu____8843 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8847 =
                let uu____8848 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8848 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8847
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8857 =
                   let uu____8858 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8858 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8857
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8866 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8866))
           in
        if uu____8843
        then
          let uu____8869 =
            let uu____8875 =
              let uu____8877 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8880 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8877 uu____8880
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8875)  in
          FStar_Errors.raise_error uu____8869 r
        else ());
       (let uu____8887 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8887 with
        | (us,lift,lift_ty) ->
            ((let uu____8901 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffectsTc")
                 in
              if uu____8901
              then
                let uu____8906 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8912 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8906 uu____8912
              else ());
             (let uu____8921 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8921 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____8939 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.source
                         in
                      let uu____8941 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.target
                         in
                      let uu____8943 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____8939 uu____8941 s uu____8943
                       in
                    let uu____8946 =
                      let uu____8953 =
                        let uu____8958 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____8958
                          (fun uu____8975  ->
                             match uu____8975 with
                             | (t,u) ->
                                 let uu____8986 =
                                   let uu____8987 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____8987
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____8986, u))
                         in
                      match uu____8953 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____9006 =
                              let uu____9007 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____9007.FStar_Syntax_Syntax.n  in
                            match uu____9006 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____9019)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____9047 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____9047 with
                                 | (a',uu____9057)::bs1 ->
                                     let uu____9077 =
                                       let uu____9078 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____9078
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____9144 =
                                       let uu____9157 =
                                         let uu____9160 =
                                           let uu____9161 =
                                             let uu____9168 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____9168)  in
                                           FStar_Syntax_Syntax.NT uu____9161
                                            in
                                         [uu____9160]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____9157
                                        in
                                     FStar_All.pipe_right uu____9077
                                       uu____9144)
                            | uu____9183 ->
                                let uu____9184 =
                                  let uu____9190 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____9190)
                                   in
                                FStar_Errors.raise_error uu____9184 r
                             in
                          let uu____9202 =
                            let uu____9213 =
                              let uu____9218 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9225 =
                                let uu____9226 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9226
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9218 r sub.FStar_Syntax_Syntax.source
                                u_a uu____9225
                               in
                            match uu____9213 with
                            | (f_sort,g) ->
                                let uu____9247 =
                                  let uu____9254 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9254
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9247, g)
                             in
                          (match uu____9202 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9321 =
                                 let uu____9326 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9327 =
                                   let uu____9328 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9328
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9326 r
                                   sub.FStar_Syntax_Syntax.target u_a
                                   uu____9327
                                  in
                               (match uu____9321 with
                                | (repr,g_repr) ->
                                    let uu____9345 =
                                      let uu____9350 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9351 =
                                        let uu____9353 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9355 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9353 uu____9355
                                         in
                                      pure_wp_uvar uu____9350 repr uu____9351
                                        r
                                       in
                                    (match uu____9345 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9367 =
                                             let uu____9368 =
                                               let uu____9369 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9369]  in
                                             let uu____9370 =
                                               let uu____9381 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9381]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9368;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9370;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9367
                                            in
                                         let uu____9414 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9417 =
                                           let uu____9418 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9418 guard_wp
                                            in
                                         (uu____9414, uu____9417))))
                       in
                    match uu____8946 with
                    | (k,g_k) ->
                        ((let uu____9428 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffectsTc")
                             in
                          if uu____9428
                          then
                            let uu____9433 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9433
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9442 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc")
                              in
                           if uu____9442
                           then
                             let uu____9447 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9447
                           else ());
                          (let sub1 =
                             let uu___1009_9453 = sub  in
                             let uu____9454 =
                               let uu____9457 =
                                 let uu____9458 =
                                   let uu____9461 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9461
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9458)  in
                               FStar_Pervasives_Native.Some uu____9457  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1009_9453.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1009_9453.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9454;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9473 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc")
                               in
                            if uu____9473
                            then
                              let uu____9478 =
                                FStar_Syntax_Print.sub_eff_to_string sub1  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9478
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
          let uu____9515 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9515  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target
           in
        let uu____9518 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9518
        then tc_layered_lift env sub
        else
          (let uu____9525 =
             let uu____9532 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source
                in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9532
              in
           match uu____9525 with
           | (a,wp_a_src) ->
               let uu____9539 =
                 let uu____9546 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9546
                  in
               (match uu____9539 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9554 =
                        let uu____9557 =
                          let uu____9558 =
                            let uu____9565 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9565)  in
                          FStar_Syntax_Syntax.NT uu____9558  in
                        [uu____9557]  in
                      FStar_Syntax_Subst.subst uu____9554 wp_b_tgt  in
                    let expected_k =
                      let uu____9573 =
                        let uu____9582 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9589 =
                          let uu____9598 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9598]  in
                        uu____9582 :: uu____9589  in
                      let uu____9623 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9573 uu____9623  in
                    let repr_type eff_name a1 wp =
                      (let uu____9645 =
                         let uu____9647 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9647  in
                       if uu____9645
                       then
                         let uu____9650 =
                           let uu____9656 =
                             let uu____9658 =
                               FStar_Ident.string_of_lid eff_name  in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9658
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9656)
                            in
                         let uu____9662 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9650 uu____9662
                       else ());
                      (let uu____9665 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9665 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9698 =
                               let uu____9699 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9699
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9698
                              in
                           let uu____9706 =
                             let uu____9707 =
                               let uu____9724 =
                                 let uu____9735 =
                                   FStar_Syntax_Syntax.as_arg a1  in
                                 let uu____9744 =
                                   let uu____9755 =
                                     FStar_Syntax_Syntax.as_arg wp  in
                                   [uu____9755]  in
                                 uu____9735 :: uu____9744  in
                               (repr, uu____9724)  in
                             FStar_Syntax_Syntax.Tm_app uu____9707  in
                           let uu____9800 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Syntax_Syntax.mk uu____9706 uu____9800)
                       in
                    let uu____9801 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9974 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9985 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9985 with
                              | (usubst,uvs1) ->
                                  let uu____10008 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____10009 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____10008, uu____10009)
                            else (env, lift_wp)  in
                          (match uu____9974 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10059 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10059))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10130 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10145 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10145 with
                              | (usubst,uvs) ->
                                  let uu____10170 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10170)
                            else ([], lift)  in
                          (match uu____10130 with
                           | (uvs,lift1) ->
                               ((let uu____10206 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10206
                                 then
                                   let uu____10210 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10210
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10216 =
                                   let uu____10223 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10223 lift1
                                    in
                                 match uu____10216 with
                                 | (lift2,comp,uu____10248) ->
                                     let uu____10249 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10249 with
                                      | (uu____10278,lift_wp,lift_elab) ->
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
                                            let uu____10310 =
                                              let uu____10321 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10321
                                               in
                                            let uu____10338 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10310, uu____10338)
                                          else
                                            (let uu____10367 =
                                               let uu____10378 =
                                                 let uu____10387 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10387)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10378
                                                in
                                             let uu____10402 =
                                               let uu____10411 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10411)  in
                                             (uu____10367, uu____10402))))))
                       in
                    (match uu____9801 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1093_10475 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1093_10475.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1093_10475.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1093_10475.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1093_10475.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1093_10475.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1093_10475.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1093_10475.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1093_10475.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1093_10475.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1093_10475.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1093_10475.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1093_10475.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1093_10475.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1093_10475.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1093_10475.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1093_10475.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1093_10475.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1093_10475.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1093_10475.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1093_10475.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1093_10475.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1093_10475.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1093_10475.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1093_10475.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1093_10475.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1093_10475.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1093_10475.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1093_10475.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1093_10475.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1093_10475.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1093_10475.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1093_10475.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1093_10475.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1093_10475.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1093_10475.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1093_10475.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1093_10475.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1093_10475.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1093_10475.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1093_10475.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1093_10475.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1093_10475.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1093_10475.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1093_10475.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1093_10475.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1093_10475.FStar_TypeChecker_Env.enable_defer_to_tac)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10508 =
                                 let uu____10513 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10513 with
                                 | (usubst,uvs1) ->
                                     let uu____10536 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10537 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10536, uu____10537)
                                  in
                               (match uu____10508 with
                                | (env2,lift2) ->
                                    let uu____10542 =
                                      let uu____10549 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10549
                                       in
                                    (match uu____10542 with
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
                                             let uu____10575 =
                                               let uu____10576 =
                                                 let uu____10593 =
                                                   let uu____10604 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ
                                                      in
                                                   let uu____10613 =
                                                     let uu____10624 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ
                                                        in
                                                     [uu____10624]  in
                                                   uu____10604 :: uu____10613
                                                    in
                                                 (lift_wp1, uu____10593)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____10576
                                                in
                                             let uu____10669 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10575 uu____10669
                                              in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10673 =
                                             let uu____10682 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10689 =
                                               let uu____10698 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10705 =
                                                 let uu____10714 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10714]  in
                                               uu____10698 :: uu____10705  in
                                             uu____10682 :: uu____10689  in
                                           let uu____10745 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10673 uu____10745
                                            in
                                         let uu____10748 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10748 with
                                          | (expected_k2,uu____10758,uu____10759)
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
                                                   let uu____10767 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10767))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10775 =
                             let uu____10777 =
                               let uu____10779 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10779
                                 FStar_List.length
                                in
                             uu____10777 <> Prims.int_one  in
                           if uu____10775
                           then
                             let uu____10802 =
                               let uu____10808 =
                                 let uu____10810 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10812 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10814 =
                                   let uu____10816 =
                                     let uu____10818 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10818
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10816
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10810 uu____10812 uu____10814
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10808)
                                in
                             FStar_Errors.raise_error uu____10802 r
                           else ());
                          (let uu____10845 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10848 =
                                  let uu____10850 =
                                    let uu____10853 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10853
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10850
                                    FStar_List.length
                                   in
                                uu____10848 <> Prims.int_one)
                              in
                           if uu____10845
                           then
                             let uu____10892 =
                               let uu____10898 =
                                 let uu____10900 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10902 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10904 =
                                   let uu____10906 =
                                     let uu____10908 =
                                       let uu____10911 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10911
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10908
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10906
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10900 uu____10902 uu____10904
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10898)
                                in
                             FStar_Errors.raise_error uu____10892 r
                           else ());
                          (let uu___1130_10953 = sub  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1130_10953.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1130_10953.FStar_Syntax_Syntax.target);
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
    fun uu____10984  ->
      fun r  ->
        match uu____10984 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____11007 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11035 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11035 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11066 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11066 c  in
                     let uu____11075 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11075, uvs1, tps1, c1))
               in
            (match uu____11007 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11095 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11095 with
                  | (tps2,c2) ->
                      let uu____11110 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11110 with
                       | (tps3,env3,us) ->
                           let uu____11128 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11128 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11154)::uu____11155 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11174 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11182 =
                                    let uu____11184 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11184  in
                                  if uu____11182
                                  then
                                    let uu____11187 =
                                      let uu____11193 =
                                        let uu____11195 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11197 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11195 uu____11197
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11193)
                                       in
                                    FStar_Errors.raise_error uu____11187 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11205 =
                                    let uu____11206 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11206
                                     in
                                  match uu____11205 with
                                  | (uvs2,t) ->
                                      let uu____11235 =
                                        let uu____11240 =
                                          let uu____11253 =
                                            let uu____11254 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11254.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11253)  in
                                        match uu____11240 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11269,c5)) -> ([], c5)
                                        | (uu____11311,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11350 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11235 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11382 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11382 with
                                               | (uu____11387,t1) ->
                                                   let uu____11389 =
                                                     let uu____11395 =
                                                       let uu____11397 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11399 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11403 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11397
                                                         uu____11399
                                                         uu____11403
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11395)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11389 r)
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
              let uu____11445 =
                let uu____11447 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____11447 FStar_Ident.string_of_id  in
              let uu____11449 =
                let uu____11451 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____11451 FStar_Ident.string_of_id  in
              let uu____11453 =
                let uu____11455 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____11455 FStar_Ident.string_of_id  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11445 uu____11449
                uu____11453
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11463 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11463 with
            | (us,t,ty) ->
                let uu____11479 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11479 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11492 =
                         let uu____11497 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11497
                           (fun uu____11514  ->
                              match uu____11514 with
                              | (t1,u) ->
                                  let uu____11525 =
                                    let uu____11526 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11526
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11525, u))
                          in
                       match uu____11492 with
                       | (a,u_a) ->
                           let uu____11534 =
                             let uu____11539 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11539
                               (fun uu____11556  ->
                                  match uu____11556 with
                                  | (t1,u) ->
                                      let uu____11567 =
                                        let uu____11568 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11568
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11567, u))
                              in
                           (match uu____11534 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11585 =
                                    let uu____11586 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11586.FStar_Syntax_Syntax.n  in
                                  match uu____11585 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11598) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11626 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11626 with
                                       | (a',uu____11636)::(b',uu____11638)::bs1
                                           ->
                                           let uu____11668 =
                                             let uu____11669 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11669
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11735 =
                                             let uu____11748 =
                                               let uu____11751 =
                                                 let uu____11752 =
                                                   let uu____11759 =
                                                     let uu____11762 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11762
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11759)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11752
                                                  in
                                               let uu____11775 =
                                                 let uu____11778 =
                                                   let uu____11779 =
                                                     let uu____11786 =
                                                       let uu____11789 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11789
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11786)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11779
                                                    in
                                                 [uu____11778]  in
                                               uu____11751 :: uu____11775  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11748
                                              in
                                           FStar_All.pipe_right uu____11668
                                             uu____11735)
                                  | uu____11810 ->
                                      let uu____11811 =
                                        let uu____11817 =
                                          let uu____11819 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11821 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11819 uu____11821
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11817)
                                         in
                                      FStar_Errors.raise_error uu____11811 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11854 =
                                  let uu____11865 =
                                    let uu____11870 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11871 =
                                      let uu____11872 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11872
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11870 r m u_a uu____11871
                                     in
                                  match uu____11865 with
                                  | (repr,g) ->
                                      let uu____11893 =
                                        let uu____11900 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11900
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11893, g)
                                   in
                                (match uu____11854 with
                                 | (f,guard_f) ->
                                     let uu____11932 =
                                       let x_a =
                                         let uu____11950 =
                                           let uu____11951 =
                                             let uu____11952 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11952
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11951
                                            in
                                         FStar_All.pipe_right uu____11950
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11968 =
                                         let uu____11973 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____11992 =
                                           let uu____11993 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____11993
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11973 r n u_b uu____11992
                                          in
                                       match uu____11968 with
                                       | (repr,g) ->
                                           let uu____12014 =
                                             let uu____12021 =
                                               let uu____12022 =
                                                 let uu____12023 =
                                                   let uu____12026 =
                                                     let uu____12029 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12029
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12026
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12023
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12022
                                                in
                                             FStar_All.pipe_right uu____12021
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____12014, g)
                                        in
                                     (match uu____11932 with
                                      | (g,guard_g) ->
                                          let uu____12073 =
                                            let uu____12078 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____12079 =
                                              let uu____12080 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____12080
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12078 r p u_b uu____12079
                                             in
                                          (match uu____12073 with
                                           | (repr,guard_repr) ->
                                               let uu____12095 =
                                                 let uu____12100 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____12101 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____12100
                                                   repr uu____12101 r
                                                  in
                                               (match uu____12095 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____12113 =
                                                        let uu____12116 =
                                                          let uu____12117 =
                                                            let uu____12118 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____12118]  in
                                                          let uu____12119 =
                                                            let uu____12130 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____12130]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12117;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12119;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12116
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12113
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
                                                     (let uu____12190 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____12190
                                                      then
                                                        let uu____12194 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____12200 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12194
                                                          uu____12200
                                                      else ());
                                                     (let uu____12210 =
                                                        let uu____12216 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12216)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12210);
                                                     (let uu____12220 =
                                                        let uu____12221 =
                                                          let uu____12224 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12224
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12221)
                                                         in
                                                      ((us1, t), uu____12220)))))))))))
  
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
            let uu____12271 =
              let uu____12273 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid  in
              FStar_All.pipe_right uu____12273 FStar_Ident.string_of_id  in
            let uu____12275 =
              let uu____12277 =
                let uu____12279 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____12279 FStar_Ident.string_of_id  in
              Prims.op_Hat " <: " uu____12277  in
            Prims.op_Hat uu____12271 uu____12275  in
          let uu____12282 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts
             in
          match uu____12282 with
          | (us,t,ty) ->
              let uu____12298 = FStar_Syntax_Subst.open_univ_vars us ty  in
              (match uu____12298 with
               | (us1,ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1
                      in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____12311 =
                       let uu____12316 = FStar_Syntax_Util.type_u ()  in
                       FStar_All.pipe_right uu____12316
                         (fun uu____12333  ->
                            match uu____12333 with
                            | (t1,u) ->
                                let uu____12344 =
                                  let uu____12345 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1
                                     in
                                  FStar_All.pipe_right uu____12345
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____12344, u))
                        in
                     match uu____12311 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____12362 =
                             let uu____12363 =
                               FStar_Syntax_Subst.compress ty1  in
                             uu____12363.FStar_Syntax_Syntax.n  in
                           match uu____12362 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____12375)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____12403 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____12403 with
                                | (a',uu____12413)::bs1 ->
                                    let uu____12433 =
                                      let uu____12434 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one))
                                         in
                                      FStar_All.pipe_right uu____12434
                                        FStar_Pervasives_Native.fst
                                       in
                                    let uu____12532 =
                                      let uu____12545 =
                                        let uu____12548 =
                                          let uu____12549 =
                                            let uu____12556 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a)
                                               in
                                            (a', uu____12556)  in
                                          FStar_Syntax_Syntax.NT uu____12549
                                           in
                                        [uu____12548]  in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____12545
                                       in
                                    FStar_All.pipe_right uu____12433
                                      uu____12532)
                           | uu____12571 ->
                               let uu____12572 =
                                 let uu____12578 =
                                   let uu____12580 =
                                     FStar_Syntax_Print.tag_of_term t  in
                                   let uu____12582 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____12580 uu____12582
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____12578)
                                  in
                               FStar_Errors.raise_error uu____12572 r
                            in
                         let bs = a :: rest_bs  in
                         let uu____12609 =
                           let uu____12620 =
                             let uu____12625 =
                               FStar_TypeChecker_Env.push_binders env bs  in
                             let uu____12626 =
                               let uu____12627 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____12627
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____12625 r m u uu____12626
                              in
                           match uu____12620 with
                           | (repr,g) ->
                               let uu____12648 =
                                 let uu____12655 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr
                                    in
                                 FStar_All.pipe_right uu____12655
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               (uu____12648, g)
                            in
                         (match uu____12609 with
                          | (f,guard_f) ->
                              let uu____12687 =
                                let uu____12692 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____12693 =
                                  let uu____12694 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____12694
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____12692 r n u uu____12693
                                 in
                              (match uu____12687 with
                               | (ret_t,guard_ret_t) ->
                                   let uu____12709 =
                                     let uu____12714 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____12715 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name
                                        in
                                     pure_wp_uvar uu____12714 ret_t
                                       uu____12715 r
                                      in
                                   (match uu____12709 with
                                    | (pure_wp_uvar1,guard_wp) ->
                                        let c =
                                          let uu____12725 =
                                            let uu____12726 =
                                              let uu____12727 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              [uu____12727]  in
                                            let uu____12728 =
                                              let uu____12739 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg
                                                 in
                                              [uu____12739]  in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____12726;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____12728;
                                              FStar_Syntax_Syntax.flags = []
                                            }  in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____12725
                                           in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c
                                           in
                                        ((let uu____12794 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc")
                                             in
                                          if uu____12794
                                          then
                                            let uu____12799 =
                                              FStar_Syntax_Print.term_to_string
                                                k
                                               in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____12799
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
                                             let uu____12809 =
                                               let uu____12810 =
                                                 FStar_All.pipe_right k
                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____12810
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta;
                                                    FStar_TypeChecker_Env.Eager_unfolding]
                                                    env)
                                                in
                                             FStar_All.pipe_right uu____12809
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us1)
                                              in
                                           (let uu____12814 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc")
                                               in
                                            if uu____12814
                                            then
                                              let uu____12819 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1)
                                                 in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____12819
                                            else ());
                                           (let uu____12829 =
                                              let uu____12835 =
                                                FStar_Util.format1
                                                  "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                  combinator_name
                                                 in
                                              (FStar_Errors.Warning_BleedingEdge_Feature,
                                                uu____12835)
                                               in
                                            FStar_Errors.log_issue r
                                              uu____12829);
                                           ((us1, t), (us1, k1)))))))))))
  