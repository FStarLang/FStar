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
                   let uu____1639 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1639 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1663 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1663 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1684 = fresh_a_and_u_a "a"  in
                              match uu____1684 with
                              | (a,u_a) ->
                                  let uu____1704 = fresh_a_and_u_a "b"  in
                                  (match uu____1704 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1733 =
                                           let uu____1734 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1734.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1733 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1746) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1774 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1774 with
                                              | (a',uu____1784)::(b',uu____1786)::bs1
                                                  ->
                                                  let uu____1816 =
                                                    let uu____1817 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1817
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1883 =
                                                    let uu____1896 =
                                                      let uu____1899 =
                                                        let uu____1900 =
                                                          let uu____1907 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1907)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1900
                                                         in
                                                      let uu____1914 =
                                                        let uu____1917 =
                                                          let uu____1918 =
                                                            let uu____1925 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1925)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1918
                                                           in
                                                        [uu____1917]  in
                                                      uu____1899 ::
                                                        uu____1914
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1896
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1816 uu____1883)
                                         | uu____1940 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1964 =
                                         let uu____1975 =
                                           let uu____1980 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1981 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1980 u_a
                                             uu____1981
                                            in
                                         match uu____1975 with
                                         | (repr1,g) ->
                                             let uu____1996 =
                                               let uu____2003 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2003
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____1996, g)
                                          in
                                       (match uu____1964 with
                                        | (f,guard_f) ->
                                            let uu____2043 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2056 =
                                                let uu____2061 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2080 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2061 u_b
                                                  uu____2080
                                                 in
                                              match uu____2056 with
                                              | (repr1,g) ->
                                                  let uu____2095 =
                                                    let uu____2102 =
                                                      let uu____2103 =
                                                        let uu____2104 =
                                                          let uu____2107 =
                                                            let uu____2110 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2110
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2107
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2104
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2103
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2102
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2095, g)
                                               in
                                            (match uu____2043 with
                                             | (g,guard_g) ->
                                                 let uu____2162 =
                                                   let uu____2167 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2168 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2167
                                                     u_b uu____2168
                                                    in
                                                 (match uu____2162 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2185 =
                                                        let uu____2190 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2191 =
                                                          let uu____2193 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname
                                                             in
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            uu____2193
                                                           in
                                                        pure_wp_uvar
                                                          uu____2190 repr1
                                                          uu____2191 r
                                                         in
                                                      (match uu____2185 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2213 =
                                                               let uu____2216
                                                                 =
                                                                 let uu____2217
                                                                   =
                                                                   let uu____2218
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2218]
                                                                    in
                                                                 let uu____2219
                                                                   =
                                                                   let uu____2230
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2230]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2217;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2219;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2216
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2213
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
                                                            (let uu____2289 =
                                                               let uu____2292
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2292
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2289)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2321 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2321 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2333 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2333 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2358 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc")
                             in
                          if uu____2358
                          then
                            let uu____2363 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2369 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2363 uu____2369
                          else ());
                         (let uu____2378 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2378 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2399 = fresh_a_and_u_a "a"  in
                                match uu____2399 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2428 =
                                        let uu____2429 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2429.FStar_Syntax_Syntax.n  in
                                      match uu____2428 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2441) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2469 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2469 with
                                           | (a',uu____2479)::bs1 ->
                                               let uu____2499 =
                                                 let uu____2500 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2500
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2598 =
                                                 let uu____2611 =
                                                   let uu____2614 =
                                                     let uu____2615 =
                                                       let uu____2622 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2622)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2615
                                                      in
                                                   [uu____2614]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2611
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2499 uu____2598)
                                      | uu____2637 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2655 =
                                      let uu____2666 =
                                        let uu____2671 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2672 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2671 u uu____2672
                                         in
                                      match uu____2666 with
                                      | (repr1,g) ->
                                          let uu____2687 =
                                            let uu____2694 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2694
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2687, g)
                                       in
                                    (match uu____2655 with
                                     | (f,guard_f) ->
                                         let uu____2734 =
                                           let uu____2739 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2740 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2739 u
                                             uu____2740
                                            in
                                         (match uu____2734 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2757 =
                                                let uu____2762 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2763 =
                                                  let uu____2765 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    uu____2765
                                                   in
                                                pure_wp_uvar uu____2762 ret_t
                                                  uu____2763 r
                                                 in
                                              (match uu____2757 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2783 =
                                                       let uu____2784 =
                                                         let uu____2785 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2785]  in
                                                       let uu____2786 =
                                                         let uu____2797 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2797]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2784;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2786;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2783
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2852 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffectsTc")
                                                        in
                                                     if uu____2852
                                                     then
                                                       let uu____2857 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type of subcomp before unification: %s\n"
                                                         uu____2857
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
                                                     (let uu____2864 =
                                                        let uu____2867 =
                                                          let uu____2868 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2868
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2867
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2864)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else =
                     let if_then_else_ts =
                       let uu____2897 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2897 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2927 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2927 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2951 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2951 with
                          | (us,t) ->
                              let uu____2970 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2970 with
                               | (uu____2987,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____2991 = fresh_a_and_u_a "a"  in
                                     match uu____2991 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3020 =
                                             let uu____3021 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3021.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3020 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3033) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3061 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3061 with
                                                | (a',uu____3071)::bs1 ->
                                                    let uu____3091 =
                                                      let uu____3092 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3092
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3190 =
                                                      let uu____3203 =
                                                        let uu____3206 =
                                                          let uu____3207 =
                                                            let uu____3214 =
                                                              let uu____3217
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3217
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3214)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3207
                                                           in
                                                        [uu____3206]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3203
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3091 uu____3190)
                                           | uu____3238 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3256 =
                                           let uu____3267 =
                                             let uu____3272 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3273 =
                                               let uu____3274 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3274
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3272 u_a
                                               uu____3273
                                              in
                                           match uu____3267 with
                                           | (repr1,g) ->
                                               let uu____3295 =
                                                 let uu____3302 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3302
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3295, g)
                                            in
                                         (match uu____3256 with
                                          | (f_bs,guard_f) ->
                                              let uu____3342 =
                                                let uu____3353 =
                                                  let uu____3358 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3359 =
                                                    let uu____3360 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3360
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3358 u_a
                                                    uu____3359
                                                   in
                                                match uu____3353 with
                                                | (repr1,g) ->
                                                    let uu____3381 =
                                                      let uu____3388 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3388
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3381, g)
                                                 in
                                              (match uu____3342 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3435 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3435
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3443 =
                                                     let uu____3448 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3467 =
                                                       let uu____3468 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3468
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3448
                                                       u_a uu____3467
                                                      in
                                                   (match uu____3443 with
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
                                                         (let uu____3528 =
                                                            let uu____3531 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3531
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3528,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else;
                   (let r =
                      let uu____3544 =
                        let uu____3547 =
                          let uu____3556 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3556 FStar_Util.must  in
                        FStar_All.pipe_right uu____3547
                          FStar_Pervasives_Native.snd
                         in
                      uu____3544.FStar_Syntax_Syntax.pos  in
                    let binder_aq_to_arg_aq aq =
                      match aq with
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3631) -> aq
                      | FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta uu____3633) ->
                          FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Implicit true)
                      | uu____3635 -> FStar_Pervasives_Native.None  in
                    let uu____3638 = if_then_else  in
                    match uu____3638 with
                    | (ite_us,ite_t,uu____3653) ->
                        let uu____3666 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3666 with
                         | (us,ite_t1) ->
                             let uu____3673 =
                               let uu____3690 =
                                 let uu____3691 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3691.FStar_Syntax_Syntax.n  in
                               match uu____3690 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3711,uu____3712) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3738 =
                                     let uu____3751 =
                                       let uu____3756 =
                                         let uu____3759 =
                                           let uu____3768 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3768
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3759
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3756
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3751
                                       (fun l  ->
                                          let uu____3924 = l  in
                                          match uu____3924 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3738 with
                                    | (f,g,p) ->
                                        let uu____3995 =
                                          let uu____3996 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3996 bs1
                                           in
                                        let uu____3997 =
                                          let uu____3998 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.map
                                                 (fun uu____4023  ->
                                                    match uu____4023 with
                                                    | (b,qual) ->
                                                        let uu____4042 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            b
                                                           in
                                                        (uu____4042,
                                                          (binder_aq_to_arg_aq
                                                             qual))))
                                             in
                                          FStar_Syntax_Syntax.mk_Tm_app
                                            ite_t1 uu____3998 r
                                           in
                                        (uu____3995, uu____3997, f, g, p))
                               | uu____4051 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3673 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____4086 =
                                    let uu____4095 = stronger_repr  in
                                    match uu____4095 with
                                    | (uu____4116,subcomp_t,subcomp_ty) ->
                                        let uu____4131 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____4131 with
                                         | (uu____4144,subcomp_t1) ->
                                             let uu____4146 =
                                               let uu____4157 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____4157 with
                                               | (uu____4172,subcomp_ty1) ->
                                                   let uu____4174 =
                                                     let uu____4175 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____4175.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____4174 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4189) ->
                                                        let uu____4210 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        (match uu____4210
                                                         with
                                                         | (bs_except_last,last_b)
                                                             ->
                                                             let uu____4316 =
                                                               FStar_All.pipe_right
                                                                 bs_except_last
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             let uu____4343 =
                                                               let uu____4346
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   last_b
                                                                   FStar_List.hd
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____4346
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             (uu____4316,
                                                               uu____4343))
                                                    | uu____4389 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             (match uu____4146 with
                                              | (aqs_except_last,last_aq) ->
                                                  let uu____4423 =
                                                    let uu____4434 =
                                                      FStar_All.pipe_right
                                                        aqs_except_last
                                                        (FStar_List.map
                                                           binder_aq_to_arg_aq)
                                                       in
                                                    let uu____4451 =
                                                      FStar_All.pipe_right
                                                        last_aq
                                                        binder_aq_to_arg_aq
                                                       in
                                                    (uu____4434, uu____4451)
                                                     in
                                                  (match uu____4423 with
                                                   | (aqs_except_last1,last_aq1)
                                                       ->
                                                       let aux t =
                                                         let tun_args =
                                                           FStar_All.pipe_right
                                                             aqs_except_last1
                                                             (FStar_List.map
                                                                (fun aq  ->
                                                                   (FStar_Syntax_Syntax.tun,
                                                                    aq)))
                                                            in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           subcomp_t1
                                                           (FStar_List.append
                                                              tun_args
                                                              [(t, last_aq1)])
                                                           r
                                                          in
                                                       let uu____4563 =
                                                         aux f_t  in
                                                       let uu____4566 =
                                                         aux g_t  in
                                                       (uu____4563,
                                                         uu____4566))))
                                     in
                                  (match uu____4086 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4583 =
                                         let aux t =
                                           let uu____4600 =
                                             let uu____4601 =
                                               let uu____4628 =
                                                 let uu____4645 =
                                                   let uu____4654 =
                                                     FStar_Syntax_Syntax.mk_Total
                                                       ite_t_applied
                                                      in
                                                   FStar_Util.Inr uu____4654
                                                    in
                                                 (uu____4645,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               (t, uu____4628,
                                                 FStar_Pervasives_Native.None)
                                                in
                                             FStar_Syntax_Syntax.Tm_ascribed
                                               uu____4601
                                              in
                                           FStar_Syntax_Syntax.mk uu____4600
                                             r
                                            in
                                         let uu____4695 = aux subcomp_f  in
                                         let uu____4696 = aux subcomp_g  in
                                         (uu____4695, uu____4696)  in
                                       (match uu____4583 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4700 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc")
                                                 in
                                              if uu____4700
                                              then
                                                let uu____4705 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4707 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4705 uu____4707
                                              else ());
                                             (let uu____4712 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4712 with
                                              | (uu____4719,uu____4720,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4723 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4723 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4725 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4725 with
                                                    | (uu____4732,uu____4733,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4737 =
                                                              let uu____4738
                                                                =
                                                                FStar_Syntax_Syntax.lid_as_fv
                                                                  FStar_Parser_Const.not_lid
                                                                  FStar_Syntax_Syntax.delta_constant
                                                                  FStar_Pervasives_Native.None
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____4738
                                                                FStar_Syntax_Syntax.fv_to_tm
                                                               in
                                                            let uu____4739 =
                                                              let uu____4740
                                                                =
                                                                FStar_All.pipe_right
                                                                  p_t
                                                                  FStar_Syntax_Syntax.as_arg
                                                                 in
                                                              [uu____4740]
                                                               in
                                                            FStar_Syntax_Syntax.mk_Tm_app
                                                              uu____4737
                                                              uu____4739 r
                                                             in
                                                          let uu____4773 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4773 g_g
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
                        (let uu____4797 =
                           let uu____4803 =
                             let uu____4805 =
                               FStar_Ident.string_of_lid
                                 ed.FStar_Syntax_Syntax.mname
                                in
                             let uu____4807 =
                               FStar_Ident.string_of_lid
                                 act.FStar_Syntax_Syntax.action_name
                                in
                             let uu____4809 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               uu____4805 uu____4807 uu____4809
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4803)
                            in
                         FStar_Errors.raise_error uu____4797 r)
                      else ();
                      (let uu____4816 =
                         let uu____4821 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4821 with
                         | (usubst,us) ->
                             let uu____4844 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4845 =
                               let uu___467_4846 = act  in
                               let uu____4847 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4848 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___467_4846.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___467_4846.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___467_4846.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4847;
                                 FStar_Syntax_Syntax.action_typ = uu____4848
                               }  in
                             (uu____4844, uu____4845)
                          in
                       match uu____4816 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4852 =
                               let uu____4853 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4853.FStar_Syntax_Syntax.n  in
                             match uu____4852 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4879 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4879
                                 then
                                   let repr_ts =
                                     let uu____4883 = repr  in
                                     match uu____4883 with
                                     | (us,t,uu____4898) -> (us, t)  in
                                   let repr1 =
                                     let uu____4916 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4916
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4926 =
                                       let uu____4927 =
                                         FStar_Syntax_Syntax.as_arg
                                           ct.FStar_Syntax_Syntax.result_typ
                                          in
                                       uu____4927 ::
                                         (ct.FStar_Syntax_Syntax.effect_args)
                                        in
                                     FStar_Syntax_Syntax.mk_Tm_app repr1
                                       uu____4926 r
                                      in
                                   let c1 =
                                     let uu____4945 =
                                       let uu____4948 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4948
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4945
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4951 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4952 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4952 with
                            | (act_typ1,uu____4960,g_t) ->
                                let uu____4962 =
                                  let uu____4969 =
                                    let uu___492_4970 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___492_4970.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___492_4970.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___492_4970.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___492_4970.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___492_4970.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___492_4970.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___492_4970.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___492_4970.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___492_4970.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___492_4970.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___492_4970.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___492_4970.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___492_4970.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___492_4970.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___492_4970.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___492_4970.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___492_4970.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___492_4970.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___492_4970.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___492_4970.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___492_4970.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___492_4970.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___492_4970.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___492_4970.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___492_4970.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___492_4970.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___492_4970.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___492_4970.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___492_4970.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___492_4970.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___492_4970.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___492_4970.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___492_4970.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___492_4970.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___492_4970.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___492_4970.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___492_4970.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___492_4970.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___492_4970.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___492_4970.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___492_4970.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___492_4970.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___492_4970.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___492_4970.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___492_4970.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___492_4970.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4969
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4962 with
                                 | (act_defn,uu____4973,g_d) ->
                                     ((let uu____4976 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffectsTc")
                                          in
                                       if uu____4976
                                       then
                                         let uu____4981 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4983 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4981 uu____4983
                                       else ());
                                      (let uu____4988 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4996 =
                                           let uu____4997 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4997.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4996 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____5007) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____5030 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____5030 with
                                              | (t,u) ->
                                                  let reason =
                                                    let uu____5045 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname
                                                       in
                                                    let uu____5047 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name
                                                       in
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      uu____5045 uu____5047
                                                     in
                                                  let uu____5050 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____5050 with
                                                   | (a_tm,uu____5070,g_tm)
                                                       ->
                                                       let uu____5084 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____5084 with
                                                        | (repr1,g) ->
                                                            let uu____5097 =
                                                              let uu____5100
                                                                =
                                                                let uu____5103
                                                                  =
                                                                  let uu____5106
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____5106
                                                                    (
                                                                    fun
                                                                    uu____5109
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5109)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____5103
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5100
                                                               in
                                                            let uu____5110 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____5097,
                                                              uu____5110))))
                                         | uu____5113 ->
                                             let uu____5114 =
                                               let uu____5120 =
                                                 let uu____5122 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname
                                                    in
                                                 let uu____5124 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name
                                                    in
                                                 let uu____5126 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   uu____5122 uu____5124
                                                   uu____5126
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____5120)
                                                in
                                             FStar_Errors.raise_error
                                               uu____5114 r
                                          in
                                       match uu____4988 with
                                       | (k,g_k) ->
                                           ((let uu____5143 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffectsTc")
                                                in
                                             if uu____5143
                                             then
                                               let uu____5148 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____5148
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____5156 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffectsTc")
                                                 in
                                              if uu____5156
                                              then
                                                let uu____5161 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____5161
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____5174 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  let uu____5176 =
                                                    FStar_Ident.string_of_lid
                                                      act1.FStar_Syntax_Syntax.action_name
                                                     in
                                                  let uu____5178 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    uu____5174 uu____5176
                                                    uu____5178
                                                   in
                                                let repr_args t =
                                                  let uu____5199 =
                                                    let uu____5200 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5200.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5199 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,a::is) ->
                                                      let uu____5252 =
                                                        let uu____5253 =
                                                          FStar_Syntax_Subst.compress
                                                            head
                                                           in
                                                        uu____5253.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____5252 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____5262,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____5272 ->
                                                           let uu____5273 =
                                                             let uu____5279 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____5279)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5273 r)
                                                  | uu____5288 ->
                                                      let uu____5289 =
                                                        let uu____5295 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5295)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____5289 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____5305 =
                                                  let uu____5306 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____5306.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5305 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____5331 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____5331 with
                                                     | (bs1,c1) ->
                                                         let uu____5338 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____5338
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
                                                              let uu____5349
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5349))
                                                | uu____5352 ->
                                                    let uu____5353 =
                                                      let uu____5359 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____5359)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____5353 r
                                                 in
                                              (let uu____5363 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffectsTc")
                                                  in
                                               if uu____5363
                                               then
                                                 let uu____5368 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5368
                                               else ());
                                              (let act2 =
                                                 let uu____5374 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5374 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___565_5388 =
                                                         act1  in
                                                       let uu____5389 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___565_5388.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___565_5388.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___565_5388.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5389
                                                       }
                                                     else
                                                       (let uu____5392 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5399
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5399
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5392
                                                        then
                                                          let uu___570_5404 =
                                                            act1  in
                                                          let uu____5405 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___570_5404.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___570_5404.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___570_5404.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___570_5404.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5405
                                                          }
                                                        else
                                                          (let uu____5408 =
                                                             let uu____5414 =
                                                               let uu____5416
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   ed.FStar_Syntax_Syntax.mname
                                                                  in
                                                               let uu____5418
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   act1.FStar_Syntax_Syntax.action_name
                                                                  in
                                                               let uu____5420
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5422
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 uu____5416
                                                                 uu____5418
                                                                 uu____5420
                                                                 uu____5422
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5414)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5408 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5447 =
                      match uu____5447 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5492 =
                        let uu____5493 = tschemes_of repr  in
                        let uu____5498 = tschemes_of return_repr  in
                        let uu____5503 = tschemes_of bind_repr  in
                        let uu____5508 = tschemes_of stronger_repr  in
                        let uu____5513 = tschemes_of if_then_else  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5493;
                          FStar_Syntax_Syntax.l_return = uu____5498;
                          FStar_Syntax_Syntax.l_bind = uu____5503;
                          FStar_Syntax_Syntax.l_subcomp = uu____5508;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5513
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5492  in
                    let uu___579_5518 = ed  in
                    let uu____5519 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___579_5518.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___579_5518.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___579_5518.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___579_5518.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5526 = signature  in
                         match uu____5526 with | (us,t,uu____5541) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5519;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___579_5518.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5579 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5579
         then
           let uu____5584 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5584
         else ());
        (let uu____5590 =
           let uu____5595 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5595 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5619 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5619  in
               let uu____5620 =
                 let uu____5627 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5627 bs  in
               (match uu____5620 with
                | (bs1,uu____5633,uu____5634) ->
                    let uu____5635 =
                      let tmp_t =
                        let uu____5645 =
                          let uu____5648 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5653  ->
                                 FStar_Pervasives_Native.Some uu____5653)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5648
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5645  in
                      let uu____5654 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5654 with
                      | (us,tmp_t1) ->
                          let uu____5671 =
                            let uu____5672 =
                              let uu____5673 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5673
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5672
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5671)
                       in
                    (match uu____5635 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5710 ->
                              let uu____5713 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5720 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5720 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5713
                              then (us, bs2)
                              else
                                (let uu____5731 =
                                   let uu____5737 =
                                     let uu____5739 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname
                                        in
                                     let uu____5741 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5743 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5739 uu____5741 uu____5743
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5737)
                                    in
                                 let uu____5747 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5731
                                   uu____5747))))
            in
         match uu____5590 with
         | (us,bs) ->
             let ed1 =
               let uu___613_5755 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___613_5755.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___613_5755.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___613_5755.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___613_5755.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___613_5755.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___613_5755.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5756 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5756 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5775 =
                    let uu____5780 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5780  in
                  (match uu____5775 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5801 =
                           match uu____5801 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5821 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5821 t  in
                               let uu____5830 =
                                 let uu____5831 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5831 t1  in
                               (us1, uu____5830)
                            in
                         let uu___627_5836 = ed1  in
                         let uu____5837 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5838 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5839 =
                           FStar_List.map
                             (fun a  ->
                                let uu___630_5847 = a  in
                                let uu____5848 =
                                  let uu____5849 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5849  in
                                let uu____5860 =
                                  let uu____5861 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5861  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___630_5847.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___630_5847.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___630_5847.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___630_5847.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5848;
                                  FStar_Syntax_Syntax.action_typ = uu____5860
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___627_5836.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___627_5836.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___627_5836.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___627_5836.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5837;
                           FStar_Syntax_Syntax.combinators = uu____5838;
                           FStar_Syntax_Syntax.actions = uu____5839;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___627_5836.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5873 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5873
                         then
                           let uu____5878 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5878
                         else ());
                        (let env =
                           let uu____5885 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5885
                             ed_bs
                            in
                         let check_and_gen' comb n env_opt uu____5920 k =
                           match uu____5920 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5940 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5940 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5949 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5949 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5950 =
                                            let uu____5957 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5957 t1
                                             in
                                          (match uu____5950 with
                                           | (t2,uu____5959,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5962 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5962 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5978 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname
                                                  in
                                               let uu____5980 =
                                                 FStar_Util.string_of_int n
                                                  in
                                               let uu____5982 =
                                                 let uu____5984 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5984
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5978 comb uu____5980
                                                 uu____5982
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5999 ->
                                               let uu____6000 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____6007 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____6007 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____6000
                                               then (g_us, t3)
                                               else
                                                 (let uu____6018 =
                                                    let uu____6024 =
                                                      let uu____6026 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      let uu____6028 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____6030 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____6026 comb
                                                        uu____6028 uu____6030
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____6024)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____6018
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____6038 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____6038
                          then
                            let uu____6043 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____6043
                          else ());
                         (let fresh_a_and_wp uu____6059 =
                            let fail t =
                              let uu____6072 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____6072
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____6088 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____6088 with
                            | (uu____6099,signature1) ->
                                let uu____6101 =
                                  let uu____6102 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____6102.FStar_Syntax_Syntax.n  in
                                (match uu____6101 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____6112) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____6141)::(wp,uu____6143)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6172 -> fail signature1)
                                 | uu____6173 -> fail signature1)
                             in
                          let log_combinator s ts =
                            let uu____6187 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____6187
                            then
                              let uu____6192 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname
                                 in
                              let uu____6194 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____6192 s uu____6194
                            else ()  in
                          let ret_wp =
                            let uu____6200 = fresh_a_and_wp ()  in
                            match uu____6200 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____6216 =
                                    let uu____6225 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____6232 =
                                      let uu____6241 =
                                        let uu____6248 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6248
                                         in
                                      [uu____6241]  in
                                    uu____6225 :: uu____6232  in
                                  let uu____6267 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____6216
                                    uu____6267
                                   in
                                let uu____6270 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6270
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6284 = fresh_a_and_wp ()  in
                             match uu____6284 with
                             | (a,wp_sort_a) ->
                                 let uu____6297 = fresh_a_and_wp ()  in
                                 (match uu____6297 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6313 =
                                          let uu____6322 =
                                            let uu____6329 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6329
                                             in
                                          [uu____6322]  in
                                        let uu____6342 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6313
                                          uu____6342
                                         in
                                      let k =
                                        let uu____6348 =
                                          let uu____6357 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6364 =
                                            let uu____6373 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6380 =
                                              let uu____6389 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6396 =
                                                let uu____6405 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6412 =
                                                  let uu____6421 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6421]  in
                                                uu____6405 :: uu____6412  in
                                              uu____6389 :: uu____6396  in
                                            uu____6373 :: uu____6380  in
                                          uu____6357 :: uu____6364  in
                                        let uu____6464 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6348
                                          uu____6464
                                         in
                                      let uu____6467 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6467
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6481 = fresh_a_and_wp ()  in
                              match uu____6481 with
                              | (a,wp_sort_a) ->
                                  let uu____6494 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6494 with
                                   | (t,uu____6500) ->
                                       let k =
                                         let uu____6504 =
                                           let uu____6513 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6520 =
                                             let uu____6529 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6536 =
                                               let uu____6545 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6545]  in
                                             uu____6529 :: uu____6536  in
                                           uu____6513 :: uu____6520  in
                                         let uu____6576 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6504
                                           uu____6576
                                          in
                                       let uu____6579 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6579
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6593 = fresh_a_and_wp ()  in
                               match uu____6593 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6607 =
                                       let uu____6610 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6610
                                        in
                                     let uu____6611 =
                                       let uu____6612 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6612
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6607
                                       uu____6611
                                      in
                                   let k =
                                     let uu____6624 =
                                       let uu____6633 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6640 =
                                         let uu____6649 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6656 =
                                           let uu____6665 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6672 =
                                             let uu____6681 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6681]  in
                                           uu____6665 :: uu____6672  in
                                         uu____6649 :: uu____6656  in
                                       uu____6633 :: uu____6640  in
                                     let uu____6718 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6624
                                       uu____6718
                                      in
                                   let uu____6721 =
                                     let uu____6726 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6726
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6721
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6758 = fresh_a_and_wp ()  in
                                match uu____6758 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6774 =
                                        let uu____6783 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6790 =
                                          let uu____6799 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6799]  in
                                        uu____6783 :: uu____6790  in
                                      let uu____6824 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6774
                                        uu____6824
                                       in
                                    let uu____6827 =
                                      let uu____6832 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6832
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6827
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6848 = fresh_a_and_wp ()  in
                                 match uu____6848 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6862 =
                                         let uu____6865 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6865
                                          in
                                       let uu____6866 =
                                         let uu____6867 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6867
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6862
                                         uu____6866
                                        in
                                     let wp_sort_b_a =
                                       let uu____6879 =
                                         let uu____6888 =
                                           let uu____6895 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6895
                                            in
                                         [uu____6888]  in
                                       let uu____6908 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6879
                                         uu____6908
                                        in
                                     let k =
                                       let uu____6914 =
                                         let uu____6923 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6930 =
                                           let uu____6939 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6946 =
                                             let uu____6955 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6955]  in
                                           uu____6939 :: uu____6946  in
                                         uu____6923 :: uu____6930  in
                                       let uu____6986 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6914
                                         uu____6986
                                        in
                                     let uu____6989 =
                                       let uu____6994 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6994
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6989
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____7010 = fresh_a_and_wp ()  in
                                  match uu____7010 with
                                  | (a,wp_sort_a) ->
                                      let uu____7023 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____7023 with
                                       | (t,uu____7029) ->
                                           let k =
                                             let uu____7033 =
                                               let uu____7042 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____7049 =
                                                 let uu____7058 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____7058]  in
                                               uu____7042 :: uu____7049  in
                                             let uu____7083 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____7033 uu____7083
                                              in
                                           let trivial =
                                             let uu____7087 =
                                               let uu____7092 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7092 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____7087
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____7107 =
                                  let uu____7124 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____7124 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____7153 ->
                                      let repr =
                                        let uu____7157 = fresh_a_and_wp ()
                                           in
                                        match uu____7157 with
                                        | (a,wp_sort_a) ->
                                            let uu____7170 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____7170 with
                                             | (t,uu____7176) ->
                                                 let k =
                                                   let uu____7180 =
                                                     let uu____7189 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____7196 =
                                                       let uu____7205 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____7205]  in
                                                     uu____7189 :: uu____7196
                                                      in
                                                   let uu____7230 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7180 uu____7230
                                                    in
                                                 let uu____7233 =
                                                   let uu____7238 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7238
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7233
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7282 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____7282 with
                                          | (uu____7289,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____7292 =
                                                let uu____7293 =
                                                  let uu____7310 =
                                                    let uu____7321 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7338 =
                                                      let uu____7349 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7349]  in
                                                    uu____7321 :: uu____7338
                                                     in
                                                  (repr2, uu____7310)  in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____7293
                                                 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7292
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7415 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7415 wp  in
                                        let destruct_repr t =
                                          let uu____7430 =
                                            let uu____7431 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7431.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7430 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7442,(t1,uu____7444)::
                                               (wp,uu____7446)::[])
                                              -> (t1, wp)
                                          | uu____7505 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7521 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7521
                                              FStar_Util.must
                                             in
                                          let uu____7548 = fresh_a_and_wp ()
                                             in
                                          match uu____7548 with
                                          | (a,uu____7556) ->
                                              let x_a =
                                                let uu____7562 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7562
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7568 =
                                                    let uu____7569 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____7569
                                                      FStar_Pervasives_Native.snd
                                                     in
                                                  let uu____7578 =
                                                    let uu____7579 =
                                                      let uu____7588 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7588
                                                        FStar_Syntax_Syntax.as_arg
                                                       in
                                                    let uu____7597 =
                                                      let uu____7608 =
                                                        let uu____7617 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7617
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      [uu____7608]  in
                                                    uu____7579 :: uu____7597
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7568 uu____7578
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7653 =
                                                  let uu____7662 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7669 =
                                                    let uu____7678 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7678]  in
                                                  uu____7662 :: uu____7669
                                                   in
                                                let uu____7703 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7653 uu____7703
                                                 in
                                              let uu____7706 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7706 with
                                               | (k1,uu____7714,uu____7715)
                                                   ->
                                                   let env1 =
                                                     let uu____7719 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7719
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
                                             let uu____7732 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7732
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7770 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7770
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7771 = fresh_a_and_wp ()
                                              in
                                           match uu____7771 with
                                           | (a,wp_sort_a) ->
                                               let uu____7784 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7784 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7800 =
                                                        let uu____7809 =
                                                          let uu____7816 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7816
                                                           in
                                                        [uu____7809]  in
                                                      let uu____7829 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7800 uu____7829
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
                                                      let uu____7837 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7837
                                                       in
                                                    let wp_g_x =
                                                      let uu____7840 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g
                                                         in
                                                      let uu____7841 =
                                                        let uu____7842 =
                                                          let uu____7851 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7851
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7842]  in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7840 uu____7841
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7880 =
                                                          let uu____7881 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7881
                                                            FStar_Pervasives_Native.snd
                                                           in
                                                        let uu____7890 =
                                                          let uu____7891 =
                                                            let uu____7894 =
                                                              let uu____7897
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a
                                                                 in
                                                              let uu____7898
                                                                =
                                                                let uu____7901
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b
                                                                   in
                                                                let uu____7902
                                                                  =
                                                                  let uu____7905
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  let uu____7906
                                                                    =
                                                                    let uu____7909
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7909]
                                                                     in
                                                                  uu____7905
                                                                    ::
                                                                    uu____7906
                                                                   in
                                                                uu____7901 ::
                                                                  uu____7902
                                                                 in
                                                              uu____7897 ::
                                                                uu____7898
                                                               in
                                                            r :: uu____7894
                                                             in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7891
                                                           in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7880
                                                          uu____7890
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7927 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7927
                                                      then
                                                        let uu____7938 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7945 =
                                                          let uu____7954 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7954]  in
                                                        uu____7938 ::
                                                          uu____7945
                                                      else []  in
                                                    let k =
                                                      let uu____7990 =
                                                        let uu____7999 =
                                                          let uu____8008 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____8015 =
                                                            let uu____8024 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____8024]  in
                                                          uu____8008 ::
                                                            uu____8015
                                                           in
                                                        let uu____8049 =
                                                          let uu____8058 =
                                                            let uu____8067 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____8074 =
                                                              let uu____8083
                                                                =
                                                                let uu____8090
                                                                  =
                                                                  let uu____8091
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____8091
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____8090
                                                                 in
                                                              let uu____8092
                                                                =
                                                                let uu____8101
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____8108
                                                                  =
                                                                  let uu____8117
                                                                    =
                                                                    let uu____8124
                                                                    =
                                                                    let uu____8125
                                                                    =
                                                                    let uu____8134
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____8134]
                                                                     in
                                                                    let uu____8153
                                                                    =
                                                                    let uu____8156
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____8156
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____8125
                                                                    uu____8153
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____8124
                                                                     in
                                                                  [uu____8117]
                                                                   in
                                                                uu____8101 ::
                                                                  uu____8108
                                                                 in
                                                              uu____8083 ::
                                                                uu____8092
                                                               in
                                                            uu____8067 ::
                                                              uu____8074
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____8058
                                                           in
                                                        FStar_List.append
                                                          uu____7999
                                                          uu____8049
                                                         in
                                                      let uu____8201 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7990 uu____8201
                                                       in
                                                    let uu____8204 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____8204 with
                                                     | (k1,uu____8212,uu____8213)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___825_8223
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___825_8223.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____8225 
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8225)
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
                                              (let uu____8252 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8266 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____8266 with
                                                    | (usubst,uvs) ->
                                                        let uu____8289 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____8290 =
                                                          let uu___838_8291 =
                                                            act  in
                                                          let uu____8292 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____8293 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___838_8291.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___838_8291.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___838_8291.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8292;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8293
                                                          }  in
                                                        (uu____8289,
                                                          uu____8290))
                                                  in
                                               match uu____8252 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____8297 =
                                                       let uu____8298 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____8298.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____8297 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____8324 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____8324
                                                         then
                                                           let uu____8327 =
                                                             let uu____8330 =
                                                               let uu____8331
                                                                 =
                                                                 let uu____8332
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8332
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8331
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8330
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8327
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8355 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8356 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8356 with
                                                    | (act_typ1,uu____8364,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___855_8367 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___855_8367.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          }  in
                                                        ((let uu____8370 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8370
                                                          then
                                                            let uu____8374 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8376 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8378 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8374
                                                              uu____8376
                                                              uu____8378
                                                          else ());
                                                         (let uu____8383 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8383
                                                          with
                                                          | (act_defn,uu____8391,g_a)
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
                                                              let uu____8395
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
                                                                    let uu____8431
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8431
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8443)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8450
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8450
                                                                     in
                                                                    let uu____8453
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8453
                                                                    with
                                                                    | 
                                                                    (k1,uu____8467,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8471
                                                                    ->
                                                                    let uu____8472
                                                                    =
                                                                    let uu____8478
                                                                    =
                                                                    let uu____8480
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8482
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8480
                                                                    uu____8482
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8478)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8472
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8395
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
                                                                    let uu____8500
                                                                    =
                                                                    let uu____8501
                                                                    =
                                                                    let uu____8502
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8502
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8501
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8500);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8504
                                                                    =
                                                                    let uu____8505
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8505.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8504
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8530
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8530
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8537
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8537
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8557
                                                                    =
                                                                    let uu____8558
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8558]
                                                                     in
                                                                    let uu____8559
                                                                    =
                                                                    let uu____8570
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8570]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8557;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8559;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8595
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8595))
                                                                    | 
                                                                    uu____8598
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8600
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8622
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8622))
                                                                     in
                                                                    match uu____8600
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
                                                                    let uu___905_8641
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___905_8641.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___905_8641.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___905_8641.FStar_Syntax_Syntax.action_params);
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
                                match uu____7107 with
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
                                      let uu____8684 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8684 ts1
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
                                          uu____8696 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8697 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8698 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___925_8701 = ed2  in
                                      let uu____8702 = cl signature  in
                                      let uu____8703 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___928_8711 = a  in
                                             let uu____8712 =
                                               let uu____8713 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8713
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8738 =
                                               let uu____8739 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8739
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___928_8711.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___928_8711.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___928_8711.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___928_8711.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8712;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8738
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___925_8701.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___925_8701.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___925_8701.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___925_8701.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8702;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8703;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___925_8701.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8765 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8765
                                      then
                                        let uu____8770 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8770
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
        let uu____8796 =
          let uu____8811 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8811 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8796 env ed quals
  
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
        let fail uu____8861 =
          let uu____8862 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8868 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8862 uu____8868  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8912)::(wp,uu____8914)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8943 -> fail ())
        | uu____8944 -> fail ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub  ->
      (let uu____8957 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc")
          in
       if uu____8957
       then
         let uu____8962 = FStar_Syntax_Print.sub_eff_to_string sub  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8962
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8979 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8979.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.target
           in
        let uu____8991 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8995 =
                let uu____8996 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8996 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8995
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____9005 =
                   let uu____9006 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____9006 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____9005
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____9014 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____9014))
           in
        if uu____8991
        then
          let uu____9017 =
            let uu____9023 =
              let uu____9025 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____9028 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____9025 uu____9028
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____9023)  in
          FStar_Errors.raise_error uu____9017 r
        else ());
       (let uu____9035 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____9035 with
        | (us,lift,lift_ty) ->
            ((let uu____9049 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffectsTc")
                 in
              if uu____9049
              then
                let uu____9054 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____9060 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____9054 uu____9060
              else ());
             (let uu____9069 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____9069 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____9087 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.source
                         in
                      let uu____9089 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.target
                         in
                      let uu____9091 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____9087 uu____9089 s uu____9091
                       in
                    let uu____9094 =
                      let uu____9101 =
                        let uu____9106 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____9106
                          (fun uu____9123  ->
                             match uu____9123 with
                             | (t,u) ->
                                 let uu____9134 =
                                   let uu____9135 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____9135
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____9134, u))
                         in
                      match uu____9101 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____9154 =
                              let uu____9155 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____9155.FStar_Syntax_Syntax.n  in
                            match uu____9154 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____9167)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____9195 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____9195 with
                                 | (a',uu____9205)::bs1 ->
                                     let uu____9225 =
                                       let uu____9226 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____9226
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____9292 =
                                       let uu____9305 =
                                         let uu____9308 =
                                           let uu____9309 =
                                             let uu____9316 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____9316)  in
                                           FStar_Syntax_Syntax.NT uu____9309
                                            in
                                         [uu____9308]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____9305
                                        in
                                     FStar_All.pipe_right uu____9225
                                       uu____9292)
                            | uu____9331 ->
                                let uu____9332 =
                                  let uu____9338 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____9338)
                                   in
                                FStar_Errors.raise_error uu____9332 r
                             in
                          let uu____9350 =
                            let uu____9361 =
                              let uu____9366 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9373 =
                                let uu____9374 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9374
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9366 r sub.FStar_Syntax_Syntax.source
                                u_a uu____9373
                               in
                            match uu____9361 with
                            | (f_sort,g) ->
                                let uu____9395 =
                                  let uu____9402 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9402
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9395, g)
                             in
                          (match uu____9350 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9469 =
                                 let uu____9474 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9475 =
                                   let uu____9476 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9476
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9474 r
                                   sub.FStar_Syntax_Syntax.target u_a
                                   uu____9475
                                  in
                               (match uu____9469 with
                                | (repr,g_repr) ->
                                    let uu____9493 =
                                      let uu____9498 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9499 =
                                        let uu____9501 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9503 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9501 uu____9503
                                         in
                                      pure_wp_uvar uu____9498 repr uu____9499
                                        r
                                       in
                                    (match uu____9493 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9515 =
                                             let uu____9516 =
                                               let uu____9517 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9517]  in
                                             let uu____9518 =
                                               let uu____9529 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9529]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9516;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9518;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9515
                                            in
                                         let uu____9562 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9565 =
                                           let uu____9566 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9566 guard_wp
                                            in
                                         (uu____9562, uu____9565))))
                       in
                    match uu____9094 with
                    | (k,g_k) ->
                        ((let uu____9576 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffectsTc")
                             in
                          if uu____9576
                          then
                            let uu____9581 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9581
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9590 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc")
                              in
                           if uu____9590
                           then
                             let uu____9595 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9595
                           else ());
                          (let sub1 =
                             let uu___1021_9601 = sub  in
                             let uu____9602 =
                               let uu____9605 =
                                 let uu____9606 =
                                   let uu____9609 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9609
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9606)  in
                               FStar_Pervasives_Native.Some uu____9605  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1021_9601.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1021_9601.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9602;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9621 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc")
                               in
                            if uu____9621
                            then
                              let uu____9626 =
                                FStar_Syntax_Print.sub_eff_to_string sub1  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9626
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
          let uu____9663 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9663  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target
           in
        let uu____9666 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9666
        then tc_layered_lift env sub
        else
          (let uu____9673 =
             let uu____9680 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source
                in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9680
              in
           match uu____9673 with
           | (a,wp_a_src) ->
               let uu____9687 =
                 let uu____9694 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9694
                  in
               (match uu____9687 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9702 =
                        let uu____9705 =
                          let uu____9706 =
                            let uu____9713 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9713)  in
                          FStar_Syntax_Syntax.NT uu____9706  in
                        [uu____9705]  in
                      FStar_Syntax_Subst.subst uu____9702 wp_b_tgt  in
                    let expected_k =
                      let uu____9721 =
                        let uu____9730 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9737 =
                          let uu____9746 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9746]  in
                        uu____9730 :: uu____9737  in
                      let uu____9771 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9721 uu____9771  in
                    let repr_type eff_name a1 wp =
                      (let uu____9793 =
                         let uu____9795 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9795  in
                       if uu____9793
                       then
                         let uu____9798 =
                           let uu____9804 =
                             let uu____9806 =
                               FStar_Ident.string_of_lid eff_name  in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9806
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9804)
                            in
                         let uu____9810 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9798 uu____9810
                       else ());
                      (let uu____9813 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9813 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9846 =
                               let uu____9847 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9847
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9846
                              in
                           let uu____9854 =
                             let uu____9855 =
                               let uu____9872 =
                                 let uu____9883 =
                                   FStar_Syntax_Syntax.as_arg a1  in
                                 let uu____9892 =
                                   let uu____9903 =
                                     FStar_Syntax_Syntax.as_arg wp  in
                                   [uu____9903]  in
                                 uu____9883 :: uu____9892  in
                               (repr, uu____9872)  in
                             FStar_Syntax_Syntax.Tm_app uu____9855  in
                           let uu____9948 =
                             FStar_TypeChecker_Env.get_range env  in
                           FStar_Syntax_Syntax.mk uu____9854 uu____9948)
                       in
                    let uu____9949 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____10122 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____10133 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____10133 with
                              | (usubst,uvs1) ->
                                  let uu____10156 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____10157 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____10156, uu____10157)
                            else (env, lift_wp)  in
                          (match uu____10122 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10207 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10207))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10278 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10293 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10293 with
                              | (usubst,uvs) ->
                                  let uu____10318 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10318)
                            else ([], lift)  in
                          (match uu____10278 with
                           | (uvs,lift1) ->
                               ((let uu____10354 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10354
                                 then
                                   let uu____10358 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10358
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10364 =
                                   let uu____10371 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10371 lift1
                                    in
                                 match uu____10364 with
                                 | (lift2,comp,uu____10396) ->
                                     let uu____10397 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10397 with
                                      | (uu____10426,lift_wp,lift_elab) ->
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
                                            let uu____10458 =
                                              let uu____10469 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10469
                                               in
                                            let uu____10486 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10458, uu____10486)
                                          else
                                            (let uu____10515 =
                                               let uu____10526 =
                                                 let uu____10535 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10535)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10526
                                                in
                                             let uu____10550 =
                                               let uu____10559 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10559)  in
                                             (uu____10515, uu____10550))))))
                       in
                    (match uu____9949 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1105_10623 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1105_10623.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1105_10623.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1105_10623.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1105_10623.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1105_10623.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1105_10623.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1105_10623.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1105_10623.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1105_10623.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1105_10623.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1105_10623.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1105_10623.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1105_10623.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1105_10623.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1105_10623.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1105_10623.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1105_10623.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1105_10623.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1105_10623.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1105_10623.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1105_10623.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1105_10623.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1105_10623.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1105_10623.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1105_10623.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1105_10623.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1105_10623.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1105_10623.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1105_10623.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1105_10623.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1105_10623.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1105_10623.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1105_10623.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1105_10623.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1105_10623.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1105_10623.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1105_10623.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1105_10623.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1105_10623.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1105_10623.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1105_10623.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1105_10623.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1105_10623.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1105_10623.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1105_10623.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1105_10623.FStar_TypeChecker_Env.enable_defer_to_tac)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10656 =
                                 let uu____10661 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10661 with
                                 | (usubst,uvs1) ->
                                     let uu____10684 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10685 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10684, uu____10685)
                                  in
                               (match uu____10656 with
                                | (env2,lift2) ->
                                    let uu____10690 =
                                      let uu____10697 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10697
                                       in
                                    (match uu____10690 with
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
                                             let uu____10723 =
                                               let uu____10724 =
                                                 let uu____10741 =
                                                   let uu____10752 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ
                                                      in
                                                   let uu____10761 =
                                                     let uu____10772 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ
                                                        in
                                                     [uu____10772]  in
                                                   uu____10752 :: uu____10761
                                                    in
                                                 (lift_wp1, uu____10741)  in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____10724
                                                in
                                             let uu____10817 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____10723 uu____10817
                                              in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10821 =
                                             let uu____10830 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10837 =
                                               let uu____10846 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10853 =
                                                 let uu____10862 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10862]  in
                                               uu____10846 :: uu____10853  in
                                             uu____10830 :: uu____10837  in
                                           let uu____10893 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10821 uu____10893
                                            in
                                         let uu____10896 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10896 with
                                          | (expected_k2,uu____10906,uu____10907)
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
                                                   let uu____10915 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10915))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10923 =
                             let uu____10925 =
                               let uu____10927 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10927
                                 FStar_List.length
                                in
                             uu____10925 <> Prims.int_one  in
                           if uu____10923
                           then
                             let uu____10950 =
                               let uu____10956 =
                                 let uu____10958 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10960 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10962 =
                                   let uu____10964 =
                                     let uu____10966 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10966
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10964
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10958 uu____10960 uu____10962
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10956)
                                in
                             FStar_Errors.raise_error uu____10950 r
                           else ());
                          (let uu____10993 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10996 =
                                  let uu____10998 =
                                    let uu____11001 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____11001
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10998
                                    FStar_List.length
                                   in
                                uu____10996 <> Prims.int_one)
                              in
                           if uu____10993
                           then
                             let uu____11040 =
                               let uu____11046 =
                                 let uu____11048 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____11050 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____11052 =
                                   let uu____11054 =
                                     let uu____11056 =
                                       let uu____11059 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____11059
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____11056
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____11054
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____11048 uu____11050 uu____11052
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____11046)
                                in
                             FStar_Errors.raise_error uu____11040 r
                           else ());
                          (let uu___1142_11101 = sub  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1142_11101.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1142_11101.FStar_Syntax_Syntax.target);
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
    fun uu____11132  ->
      fun r  ->
        match uu____11132 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____11155 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11183 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11183 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11214 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11214 c  in
                     let uu____11223 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11223, uvs1, tps1, c1))
               in
            (match uu____11155 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11243 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11243 with
                  | (tps2,c2) ->
                      let uu____11258 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11258 with
                       | (tps3,env3,us) ->
                           let uu____11276 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11276 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11302)::uu____11303 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11322 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11330 =
                                    let uu____11332 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11332  in
                                  if uu____11330
                                  then
                                    let uu____11335 =
                                      let uu____11341 =
                                        let uu____11343 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11345 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11343 uu____11345
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11341)
                                       in
                                    FStar_Errors.raise_error uu____11335 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11353 =
                                    let uu____11354 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11354
                                     in
                                  match uu____11353 with
                                  | (uvs2,t) ->
                                      let uu____11383 =
                                        let uu____11388 =
                                          let uu____11401 =
                                            let uu____11402 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11402.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11401)  in
                                        match uu____11388 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11417,c5)) -> ([], c5)
                                        | (uu____11459,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11498 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11383 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11530 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11530 with
                                               | (uu____11535,t1) ->
                                                   let uu____11537 =
                                                     let uu____11543 =
                                                       let uu____11545 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11547 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11551 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11545
                                                         uu____11547
                                                         uu____11551
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11543)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11537 r)
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
              let uu____11593 =
                let uu____11595 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____11595 FStar_Ident.string_of_id  in
              let uu____11597 =
                let uu____11599 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____11599 FStar_Ident.string_of_id  in
              let uu____11601 =
                let uu____11603 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____11603 FStar_Ident.string_of_id  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11593 uu____11597
                uu____11601
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11611 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11611 with
            | (us,t,ty) ->
                let uu____11627 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11627 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11640 =
                         let uu____11645 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11645
                           (fun uu____11662  ->
                              match uu____11662 with
                              | (t1,u) ->
                                  let uu____11673 =
                                    let uu____11674 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11674
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11673, u))
                          in
                       match uu____11640 with
                       | (a,u_a) ->
                           let uu____11682 =
                             let uu____11687 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11687
                               (fun uu____11704  ->
                                  match uu____11704 with
                                  | (t1,u) ->
                                      let uu____11715 =
                                        let uu____11716 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11716
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11715, u))
                              in
                           (match uu____11682 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11733 =
                                    let uu____11734 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11734.FStar_Syntax_Syntax.n  in
                                  match uu____11733 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11746) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11774 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11774 with
                                       | (a',uu____11784)::(b',uu____11786)::bs1
                                           ->
                                           let uu____11816 =
                                             let uu____11817 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11817
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11883 =
                                             let uu____11896 =
                                               let uu____11899 =
                                                 let uu____11900 =
                                                   let uu____11907 =
                                                     let uu____11910 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11910
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11907)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11900
                                                  in
                                               let uu____11923 =
                                                 let uu____11926 =
                                                   let uu____11927 =
                                                     let uu____11934 =
                                                       let uu____11937 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11937
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11934)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11927
                                                    in
                                                 [uu____11926]  in
                                               uu____11899 :: uu____11923  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11896
                                              in
                                           FStar_All.pipe_right uu____11816
                                             uu____11883)
                                  | uu____11958 ->
                                      let uu____11959 =
                                        let uu____11965 =
                                          let uu____11967 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11969 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11967 uu____11969
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11965)
                                         in
                                      FStar_Errors.raise_error uu____11959 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____12002 =
                                  let uu____12013 =
                                    let uu____12018 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____12019 =
                                      let uu____12020 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____12020
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____12018 r m u_a uu____12019
                                     in
                                  match uu____12013 with
                                  | (repr,g) ->
                                      let uu____12041 =
                                        let uu____12048 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____12048
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____12041, g)
                                   in
                                (match uu____12002 with
                                 | (f,guard_f) ->
                                     let uu____12080 =
                                       let x_a =
                                         let uu____12098 =
                                           let uu____12099 =
                                             let uu____12100 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____12100
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____12099
                                            in
                                         FStar_All.pipe_right uu____12098
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____12116 =
                                         let uu____12121 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____12140 =
                                           let uu____12141 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____12141
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____12121 r n u_b uu____12140
                                          in
                                       match uu____12116 with
                                       | (repr,g) ->
                                           let uu____12162 =
                                             let uu____12169 =
                                               let uu____12170 =
                                                 let uu____12171 =
                                                   let uu____12174 =
                                                     let uu____12177 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12177
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12174
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12171
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12170
                                                in
                                             FStar_All.pipe_right uu____12169
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____12162, g)
                                        in
                                     (match uu____12080 with
                                      | (g,guard_g) ->
                                          let uu____12221 =
                                            let uu____12226 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____12227 =
                                              let uu____12228 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____12228
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12226 r p u_b uu____12227
                                             in
                                          (match uu____12221 with
                                           | (repr,guard_repr) ->
                                               let uu____12243 =
                                                 let uu____12248 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____12249 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____12248
                                                   repr uu____12249 r
                                                  in
                                               (match uu____12243 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____12261 =
                                                        let uu____12264 =
                                                          let uu____12265 =
                                                            let uu____12266 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____12266]  in
                                                          let uu____12267 =
                                                            let uu____12278 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____12278]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12265;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12267;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12264
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12261
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
                                                     (let uu____12338 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____12338
                                                      then
                                                        let uu____12342 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____12348 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12342
                                                          uu____12348
                                                      else ());
                                                     (let uu____12358 =
                                                        let uu____12364 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12364)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12358);
                                                     (let uu____12368 =
                                                        let uu____12369 =
                                                          let uu____12372 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12372
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12369)
                                                         in
                                                      ((us1, t), uu____12368)))))))))))
  
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
            let uu____12419 =
              let uu____12421 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid  in
              FStar_All.pipe_right uu____12421 FStar_Ident.string_of_id  in
            let uu____12423 =
              let uu____12425 =
                let uu____12427 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid  in
                FStar_All.pipe_right uu____12427 FStar_Ident.string_of_id  in
              Prims.op_Hat " <: " uu____12425  in
            Prims.op_Hat uu____12419 uu____12423  in
          let uu____12430 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts
             in
          match uu____12430 with
          | (us,t,ty) ->
              let uu____12446 = FStar_Syntax_Subst.open_univ_vars us ty  in
              (match uu____12446 with
               | (us1,ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1
                      in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____12459 =
                       let uu____12464 = FStar_Syntax_Util.type_u ()  in
                       FStar_All.pipe_right uu____12464
                         (fun uu____12481  ->
                            match uu____12481 with
                            | (t1,u) ->
                                let uu____12492 =
                                  let uu____12493 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1
                                     in
                                  FStar_All.pipe_right uu____12493
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____12492, u))
                        in
                     match uu____12459 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____12510 =
                             let uu____12511 =
                               FStar_Syntax_Subst.compress ty1  in
                             uu____12511.FStar_Syntax_Syntax.n  in
                           match uu____12510 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs,uu____12523)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____12551 =
                                 FStar_Syntax_Subst.open_binders bs  in
                               (match uu____12551 with
                                | (a',uu____12561)::bs1 ->
                                    let uu____12581 =
                                      let uu____12582 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one))
                                         in
                                      FStar_All.pipe_right uu____12582
                                        FStar_Pervasives_Native.fst
                                       in
                                    let uu____12680 =
                                      let uu____12693 =
                                        let uu____12696 =
                                          let uu____12697 =
                                            let uu____12704 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a)
                                               in
                                            (a', uu____12704)  in
                                          FStar_Syntax_Syntax.NT uu____12697
                                           in
                                        [uu____12696]  in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____12693
                                       in
                                    FStar_All.pipe_right uu____12581
                                      uu____12680)
                           | uu____12719 ->
                               let uu____12720 =
                                 let uu____12726 =
                                   let uu____12728 =
                                     FStar_Syntax_Print.tag_of_term t  in
                                   let uu____12730 =
                                     FStar_Syntax_Print.term_to_string t  in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____12728 uu____12730
                                    in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____12726)
                                  in
                               FStar_Errors.raise_error uu____12720 r
                            in
                         let bs = a :: rest_bs  in
                         let uu____12757 =
                           let uu____12768 =
                             let uu____12773 =
                               FStar_TypeChecker_Env.push_binders env bs  in
                             let uu____12774 =
                               let uu____12775 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____12775
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____12773 r m u uu____12774
                              in
                           match uu____12768 with
                           | (repr,g) ->
                               let uu____12796 =
                                 let uu____12803 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr
                                    in
                                 FStar_All.pipe_right uu____12803
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               (uu____12796, g)
                            in
                         (match uu____12757 with
                          | (f,guard_f) ->
                              let uu____12835 =
                                let uu____12840 =
                                  FStar_TypeChecker_Env.push_binders env bs
                                   in
                                let uu____12841 =
                                  let uu____12842 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____12842
                                    FStar_Syntax_Syntax.bv_to_name
                                   in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____12840 r n u uu____12841
                                 in
                              (match uu____12835 with
                               | (ret_t,guard_ret_t) ->
                                   let uu____12857 =
                                     let uu____12862 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs
                                        in
                                     let uu____12863 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name
                                        in
                                     pure_wp_uvar uu____12862 ret_t
                                       uu____12863 r
                                      in
                                   (match uu____12857 with
                                    | (pure_wp_uvar1,guard_wp) ->
                                        let c =
                                          let uu____12873 =
                                            let uu____12874 =
                                              let uu____12875 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  ()
                                                 in
                                              [uu____12875]  in
                                            let uu____12876 =
                                              let uu____12887 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg
                                                 in
                                              [uu____12887]  in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____12874;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____12876;
                                              FStar_Syntax_Syntax.flags = []
                                            }  in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____12873
                                           in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c
                                           in
                                        ((let uu____12942 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc")
                                             in
                                          if uu____12942
                                          then
                                            let uu____12947 =
                                              FStar_Syntax_Print.term_to_string
                                                k
                                               in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____12947
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
                                             let uu____12957 =
                                               let uu____12958 =
                                                 FStar_All.pipe_right k
                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                      env)
                                                  in
                                               FStar_All.pipe_right
                                                 uu____12958
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta;
                                                    FStar_TypeChecker_Env.Eager_unfolding]
                                                    env)
                                                in
                                             FStar_All.pipe_right uu____12957
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us1)
                                              in
                                           (let uu____12962 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc")
                                               in
                                            if uu____12962
                                            then
                                              let uu____12967 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1)
                                                 in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____12967
                                            else ());
                                           (let uu____12977 =
                                              let uu____12983 =
                                                FStar_Util.format1
                                                  "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                  combinator_name
                                                 in
                                              (FStar_Errors.Warning_BleedingEdge_Feature,
                                                uu____12983)
                                               in
                                            FStar_Errors.log_issue r
                                              uu____12977);
                                           ((us1, t), (us1, k1)))))))))))
  