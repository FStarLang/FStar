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
                  let uu____246 =
                    let uu____247 =
                      FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg  in
                    [uu____247]  in
                  FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____246  in
                uu____241 FStar_Pervasives_Native.None r
             in
          let uu____280 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t
             in
          match uu____280 with
          | (pure_wp_uvar,uu____298,guard_wp) -> (pure_wp_uvar, guard_wp)
  
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env  ->
    fun t  ->
      fun k  ->
        (let uu____333 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____333
         then
           let uu____338 = FStar_Syntax_Print.term_to_string t  in
           let uu____340 =
             match k with
             | FStar_Pervasives_Native.None  -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1
              in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____338 uu____340
         else ());
        (let env1 =
           let uu___54_349 = env  in
           {
             FStar_TypeChecker_Env.solver =
               (uu___54_349.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___54_349.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___54_349.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___54_349.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___54_349.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___54_349.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___54_349.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___54_349.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___54_349.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___54_349.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___54_349.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___54_349.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___54_349.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___54_349.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___54_349.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___54_349.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___54_349.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict = true;
             FStar_TypeChecker_Env.is_iface =
               (uu___54_349.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___54_349.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___54_349.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___54_349.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___54_349.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___54_349.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___54_349.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___54_349.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___54_349.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___54_349.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___54_349.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___54_349.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___54_349.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___54_349.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___54_349.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___54_349.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___54_349.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___54_349.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___54_349.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___54_349.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___54_349.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___54_349.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___54_349.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___54_349.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___54_349.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___54_349.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___54_349.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___54_349.FStar_TypeChecker_Env.erasable_types_tab)
           }  in
         match k with
         | FStar_Pervasives_Native.None  ->
             let uu____351 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t
                in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____357 =
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
        (let uu____379 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____379
         then
           let uu____384 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____384
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____402 =
             let uu____408 =
               let uu____410 =
                 let uu____412 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 Prims.op_Hat uu____412 ")"  in
               Prims.op_Hat "Binders are not supported for layered effects ("
                 uu____410
                in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____408)  in
           let uu____417 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error uu____402 uu____417)
        else ();
        (let log_combinator s uu____443 =
           match uu____443 with
           | (us,t,ty) ->
               let uu____472 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____472
               then
                 let uu____477 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
                 let uu____479 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____485 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____477 s
                   uu____479 uu____485
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____510 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____510
             (fun uu____527  ->
                match uu____527 with
                | (t,u) ->
                    let uu____538 =
                      let uu____539 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____539
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____538, u))
            in
         let fresh_x_a x a =
           let uu____553 =
             let uu____554 =
               let uu____555 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____555 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____554
              in
           FStar_All.pipe_right uu____553 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           let uu____589 =
             FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname  in
           check_and_gen env0 uu____589  in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____609 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____609 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____633 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____633 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____653 = fresh_a_and_u_a "a"  in
                    (match uu____653 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____674 =
                             let uu____675 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____675
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____674
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____706 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____706  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____711 =
                             let uu____714 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____714
                              in
                           (sig_us, uu____711, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____723 =
            let repr_ts =
              let uu____745 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____745 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____773 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____773 with
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
                  let uu____804 =
                    let uu____805 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____805.FStar_Syntax_Syntax.n  in
                  match uu____804 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____808,t,uu____810) ->
                      let uu____835 =
                        let uu____836 = FStar_Syntax_Subst.compress t  in
                        uu____836.FStar_Syntax_Syntax.n  in
                      (match uu____835 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____839,c) ->
                           let uu____861 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____861
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____864 ->
                           let uu____865 =
                             let uu____871 =
                               let uu____873 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____876 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____873 uu____876
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____871)
                              in
                           FStar_Errors.raise_error uu____865 r)
                  | uu____880 ->
                      let uu____881 =
                        let uu____887 =
                          let uu____889 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____892 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____889 uu____892
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____887)  in
                      FStar_Errors.raise_error uu____881 r
                   in
                ((let uu____897 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____903 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____903)
                     in
                  if uu____897
                  then
                    let uu____906 =
                      let uu____912 =
                        let uu____914 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____917 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____914 uu____917
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____912)
                       in
                    FStar_Errors.raise_error uu____906 r
                  else ());
                 (let uu____924 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____924 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____948 = fresh_a_and_u_a "a"  in
                      (match uu____948 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____974 = signature  in
                               match uu____974 with
                               | (us1,t,uu____989) -> (us1, t)  in
                             let uu____1006 =
                               let uu____1007 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____1007
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____1006
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1034 =
                               let uu____1037 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1037
                                 (fun uu____1050  ->
                                    match uu____1050 with
                                    | (t,u1) ->
                                        let uu____1057 =
                                          let uu____1060 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1060
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1057)
                                in
                             FStar_Syntax_Util.arrow bs uu____1034  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1063 =
                               let uu____1076 =
                                 let uu____1079 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1079
                                  in
                               (repr_us, repr_t, uu____1076)  in
                             (uu____1063, underlying_effect_lid))))))
             in
          match uu____723 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1152 = signature  in
                    match uu____1152 with | (us,t,uu____1167) -> (us, t)  in
                  let repr_ts =
                    let uu____1185 = repr  in
                    match uu____1185 with | (us,t,uu____1200) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n t r =
                  let uu____1250 =
                    let uu____1256 =
                      let uu____1258 =
                        FStar_Ident.string_of_lid
                          ed.FStar_Syntax_Syntax.mname
                         in
                      let uu____1260 = FStar_Util.string_of_int n  in
                      let uu____1262 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1264 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        uu____1258 comb uu____1260 uu____1262 uu____1264
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1256)  in
                  FStar_Errors.raise_error uu____1250 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1294 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1294 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1322 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1322 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1346 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1346 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1367 = fresh_a_and_u_a "a"  in
                             match uu____1367 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1398 =
                                     let uu____1399 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1399.FStar_Syntax_Syntax.n  in
                                   match uu____1398 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1411) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1439 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1439 with
                                        | (a',uu____1449)::(x',uu____1451)::bs1
                                            ->
                                            let uu____1481 =
                                              let uu____1482 =
                                                let uu____1487 =
                                                  let uu____1490 =
                                                    let uu____1491 =
                                                      let uu____1498 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1498)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1491
                                                     in
                                                  [uu____1490]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1487
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1482
                                               in
                                            let uu____1505 =
                                              let uu____1518 =
                                                let uu____1521 =
                                                  let uu____1522 =
                                                    let uu____1529 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1529)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1522
                                                   in
                                                [uu____1521]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1518
                                               in
                                            FStar_All.pipe_right uu____1481
                                              uu____1505)
                                   | uu____1544 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1568 =
                                   let uu____1573 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1574 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1573 u_a uu____1574  in
                                 (match uu____1568 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1594 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1594
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1599 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1599);
                                       (let uu____1600 =
                                          let uu____1603 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1603
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1600)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1632 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1632 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1660 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1660 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1684 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1684 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1705 = fresh_a_and_u_a "a"  in
                              match uu____1705 with
                              | (a,u_a) ->
                                  let uu____1725 = fresh_a_and_u_a "b"  in
                                  (match uu____1725 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1754 =
                                           let uu____1755 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1755.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1754 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1767) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1795 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1795 with
                                              | (a',uu____1805)::(b',uu____1807)::bs1
                                                  ->
                                                  let uu____1837 =
                                                    let uu____1838 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1838
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1904 =
                                                    let uu____1917 =
                                                      let uu____1920 =
                                                        let uu____1921 =
                                                          let uu____1928 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1928)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1921
                                                         in
                                                      let uu____1935 =
                                                        let uu____1938 =
                                                          let uu____1939 =
                                                            let uu____1946 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1946)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1939
                                                           in
                                                        [uu____1938]  in
                                                      uu____1920 ::
                                                        uu____1935
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1917
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1837 uu____1904)
                                         | uu____1961 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1985 =
                                         let uu____1996 =
                                           let uu____2001 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2002 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2001 u_a
                                             uu____2002
                                            in
                                         match uu____1996 with
                                         | (repr1,g) ->
                                             let uu____2017 =
                                               let uu____2024 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2024
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2017, g)
                                          in
                                       (match uu____1985 with
                                        | (f,guard_f) ->
                                            let uu____2064 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2077 =
                                                let uu____2082 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2101 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2082 u_b
                                                  uu____2101
                                                 in
                                              match uu____2077 with
                                              | (repr1,g) ->
                                                  let uu____2116 =
                                                    let uu____2123 =
                                                      let uu____2124 =
                                                        let uu____2125 =
                                                          let uu____2128 =
                                                            let uu____2131 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2131
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2128
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2125
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2124
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2123
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2116, g)
                                               in
                                            (match uu____2064 with
                                             | (g,guard_g) ->
                                                 let uu____2183 =
                                                   let uu____2188 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2189 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2188
                                                     u_b uu____2189
                                                    in
                                                 (match uu____2183 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2206 =
                                                        let uu____2211 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2212 =
                                                          let uu____2214 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname
                                                             in
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            uu____2214
                                                           in
                                                        pure_wp_uvar
                                                          uu____2211 repr1
                                                          uu____2212 r
                                                         in
                                                      (match uu____2206 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2234 =
                                                               let uu____2237
                                                                 =
                                                                 let uu____2238
                                                                   =
                                                                   let uu____2239
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2239]
                                                                    in
                                                                 let uu____2240
                                                                   =
                                                                   let uu____2251
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2251]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2238;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2240;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2237
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2234
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
                                                            (let uu____2310 =
                                                               let uu____2313
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2313
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2310)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2342 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2342 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2370 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2370 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2395 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2395
                          then
                            let uu____2400 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2406 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2400 uu____2406
                          else ());
                         (let uu____2415 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2415 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2436 = fresh_a_and_u_a "a"  in
                                match uu____2436 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2465 =
                                        let uu____2466 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2466.FStar_Syntax_Syntax.n  in
                                      match uu____2465 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2478) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2506 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2506 with
                                           | (a',uu____2516)::bs1 ->
                                               let uu____2536 =
                                                 let uu____2537 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2537
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2635 =
                                                 let uu____2648 =
                                                   let uu____2651 =
                                                     let uu____2652 =
                                                       let uu____2659 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2659)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2652
                                                      in
                                                   [uu____2651]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2648
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2536 uu____2635)
                                      | uu____2674 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2692 =
                                      let uu____2703 =
                                        let uu____2708 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2709 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2708 u uu____2709
                                         in
                                      match uu____2703 with
                                      | (repr1,g) ->
                                          let uu____2724 =
                                            let uu____2731 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2731
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2724, g)
                                       in
                                    (match uu____2692 with
                                     | (f,guard_f) ->
                                         let uu____2771 =
                                           let uu____2776 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2777 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2776 u
                                             uu____2777
                                            in
                                         (match uu____2771 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2794 =
                                                let uu____2799 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2800 =
                                                  let uu____2802 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    uu____2802
                                                   in
                                                pure_wp_uvar uu____2799 ret_t
                                                  uu____2800 r
                                                 in
                                              (match uu____2794 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2820 =
                                                       let uu____2821 =
                                                         let uu____2822 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2822]  in
                                                       let uu____2823 =
                                                         let uu____2834 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2834]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2821;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2823;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2820
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2889 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2889
                                                     then
                                                       let uu____2894 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2894
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
                                                     (let uu____2901 =
                                                        let uu____2904 =
                                                          let uu____2905 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2905
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2904
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2901)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else =
                     let if_then_else_ts =
                       let uu____2936 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2936 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2976 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2976 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____3000 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____3000 with
                          | (us,t) ->
                              let uu____3019 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____3019 with
                               | (uu____3036,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____3040 = fresh_a_and_u_a "a"  in
                                     match uu____3040 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3069 =
                                             let uu____3070 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3070.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3069 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3082) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3110 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3110 with
                                                | (a',uu____3120)::bs1 ->
                                                    let uu____3140 =
                                                      let uu____3141 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3141
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3239 =
                                                      let uu____3252 =
                                                        let uu____3255 =
                                                          let uu____3256 =
                                                            let uu____3263 =
                                                              let uu____3266
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3266
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3263)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3256
                                                           in
                                                        [uu____3255]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3252
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3140 uu____3239)
                                           | uu____3287 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3305 =
                                           let uu____3316 =
                                             let uu____3321 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3322 =
                                               let uu____3323 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3323
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3321 u_a
                                               uu____3322
                                              in
                                           match uu____3316 with
                                           | (repr1,g) ->
                                               let uu____3344 =
                                                 let uu____3351 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3351
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3344, g)
                                            in
                                         (match uu____3305 with
                                          | (f_bs,guard_f) ->
                                              let uu____3391 =
                                                let uu____3402 =
                                                  let uu____3407 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3408 =
                                                    let uu____3409 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3409
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3407 u_a
                                                    uu____3408
                                                   in
                                                match uu____3402 with
                                                | (repr1,g) ->
                                                    let uu____3430 =
                                                      let uu____3437 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3437
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3430, g)
                                                 in
                                              (match uu____3391 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3484 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3484
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3492 =
                                                     let uu____3497 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3516 =
                                                       let uu____3517 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3517
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3497
                                                       u_a uu____3516
                                                      in
                                                   (match uu____3492 with
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
                                                         (let uu____3577 =
                                                            let uu____3580 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3580
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3577,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else;
                   (let r =
                      let uu____3593 =
                        let uu____3596 =
                          let uu____3605 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3605 FStar_Util.must  in
                        FStar_All.pipe_right uu____3596
                          FStar_Pervasives_Native.snd
                         in
                      uu____3593.FStar_Syntax_Syntax.pos  in
                    let uu____3666 = if_then_else  in
                    match uu____3666 with
                    | (ite_us,ite_t,uu____3681) ->
                        let uu____3694 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3694 with
                         | (us,ite_t1) ->
                             let uu____3701 =
                               let uu____3716 =
                                 let uu____3717 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3717.FStar_Syntax_Syntax.n  in
                               match uu____3716 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3735,uu____3736) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3762 =
                                     let uu____3775 =
                                       let uu____3780 =
                                         let uu____3783 =
                                           let uu____3792 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3792
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3783
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3780
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3775
                                       (fun l  ->
                                          let uu____3948 = l  in
                                          match uu____3948 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3762 with
                                    | (f,g,p) ->
                                        let uu____4017 =
                                          let uu____4018 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____4018 bs1
                                           in
                                        let uu____4019 =
                                          let uu____4020 =
                                            let uu____4025 =
                                              let uu____4026 =
                                                let uu____4029 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4029
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____4026
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____4025
                                             in
                                          uu____4020
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____4017, uu____4019, f, g, p))
                               | uu____4060 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3701 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____4089 =
                                    let uu____4098 = stronger_repr  in
                                    match uu____4098 with
                                    | (uu____4119,subcomp_t,subcomp_ty) ->
                                        let uu____4134 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____4134 with
                                         | (uu____4147,subcomp_t1) ->
                                             let uu____4149 =
                                               let uu____4160 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____4160 with
                                               | (uu____4175,subcomp_ty1) ->
                                                   let uu____4177 =
                                                     let uu____4178 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____4178.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____4177 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4192) ->
                                                        let uu____4213 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        (match uu____4213
                                                         with
                                                         | (bs_except_last,last_b)
                                                             ->
                                                             let uu____4319 =
                                                               FStar_All.pipe_right
                                                                 bs_except_last
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             let uu____4346 =
                                                               let uu____4349
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   last_b
                                                                   FStar_List.hd
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____4349
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             (uu____4319,
                                                               uu____4346))
                                                    | uu____4392 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             (match uu____4149 with
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
                                                         [(t, last_aq)])
                                                      FStar_Pervasives_Native.None
                                                      r
                                                     in
                                                  let uu____4505 = aux f_t
                                                     in
                                                  let uu____4508 = aux g_t
                                                     in
                                                  (uu____4505, uu____4508)))
                                     in
                                  (match uu____4089 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4525 =
                                         let aux t =
                                           let uu____4542 =
                                             let uu____4549 =
                                               let uu____4550 =
                                                 let uu____4577 =
                                                   let uu____4594 =
                                                     let uu____4603 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4603
                                                      in
                                                   (uu____4594,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4577,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4550
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4549
                                              in
                                           uu____4542
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4644 = aux subcomp_f  in
                                         let uu____4645 = aux subcomp_g  in
                                         (uu____4644, uu____4645)  in
                                       (match uu____4525 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4649 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4649
                                              then
                                                let uu____4654 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4656 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4654 uu____4656
                                              else ());
                                             (let uu____4661 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4661 with
                                              | (uu____4668,uu____4669,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4672 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4672 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4674 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4674 with
                                                    | (uu____4681,uu____4682,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4688 =
                                                              let uu____4693
                                                                =
                                                                let uu____4694
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4694
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4695
                                                                =
                                                                let uu____4696
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4696]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4693
                                                                uu____4695
                                                               in
                                                            uu____4688
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4729 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4729 g_g
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
                        (let uu____4753 =
                           let uu____4759 =
                             let uu____4761 =
                               FStar_Ident.string_of_lid
                                 ed.FStar_Syntax_Syntax.mname
                                in
                             let uu____4763 =
                               FStar_Ident.string_of_lid
                                 act.FStar_Syntax_Syntax.action_name
                                in
                             let uu____4765 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               uu____4761 uu____4763 uu____4765
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4759)
                            in
                         FStar_Errors.raise_error uu____4753 r)
                      else ();
                      (let uu____4772 =
                         let uu____4777 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4777 with
                         | (usubst,us) ->
                             let uu____4800 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4801 =
                               let uu___452_4802 = act  in
                               let uu____4803 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4804 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___452_4802.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___452_4802.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___452_4802.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4803;
                                 FStar_Syntax_Syntax.action_typ = uu____4804
                               }  in
                             (uu____4800, uu____4801)
                          in
                       match uu____4772 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4808 =
                               let uu____4809 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4809.FStar_Syntax_Syntax.n  in
                             match uu____4808 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4835 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4835
                                 then
                                   let repr_ts =
                                     let uu____4839 = repr  in
                                     match uu____4839 with
                                     | (us,t,uu____4854) -> (us, t)  in
                                   let repr1 =
                                     let uu____4872 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4872
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4884 =
                                       let uu____4889 =
                                         let uu____4890 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4890 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4889
                                        in
                                     uu____4884 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4908 =
                                       let uu____4911 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4911
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4908
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4914 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4915 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4915 with
                            | (act_typ1,uu____4923,g_t) ->
                                let uu____4925 =
                                  let uu____4932 =
                                    let uu___477_4933 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___477_4933.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___477_4933.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___477_4933.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___477_4933.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___477_4933.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___477_4933.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___477_4933.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___477_4933.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___477_4933.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___477_4933.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___477_4933.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___477_4933.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___477_4933.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___477_4933.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___477_4933.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___477_4933.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___477_4933.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___477_4933.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___477_4933.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___477_4933.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___477_4933.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___477_4933.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___477_4933.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___477_4933.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___477_4933.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___477_4933.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___477_4933.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___477_4933.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___477_4933.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___477_4933.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___477_4933.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___477_4933.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___477_4933.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___477_4933.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___477_4933.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___477_4933.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___477_4933.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___477_4933.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___477_4933.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___477_4933.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___477_4933.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___477_4933.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___477_4933.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___477_4933.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___477_4933.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4932
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4925 with
                                 | (act_defn,uu____4936,g_d) ->
                                     ((let uu____4939 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4939
                                       then
                                         let uu____4944 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4946 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4944 uu____4946
                                       else ());
                                      (let uu____4951 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4959 =
                                           let uu____4960 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4960.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4959 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4970) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4993 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4993 with
                                              | (t,u) ->
                                                  let reason =
                                                    let uu____5008 =
                                                      FStar_Ident.string_of_lid
                                                        ed.FStar_Syntax_Syntax.mname
                                                       in
                                                    let uu____5010 =
                                                      FStar_Ident.string_of_lid
                                                        act1.FStar_Syntax_Syntax.action_name
                                                       in
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      uu____5008 uu____5010
                                                     in
                                                  let uu____5013 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____5013 with
                                                   | (a_tm,uu____5033,g_tm)
                                                       ->
                                                       let uu____5047 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____5047 with
                                                        | (repr1,g) ->
                                                            let uu____5060 =
                                                              let uu____5063
                                                                =
                                                                let uu____5066
                                                                  =
                                                                  let uu____5069
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____5069
                                                                    (
                                                                    fun
                                                                    uu____5072
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5072)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____5066
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5063
                                                               in
                                                            let uu____5073 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____5060,
                                                              uu____5073))))
                                         | uu____5076 ->
                                             let uu____5077 =
                                               let uu____5083 =
                                                 let uu____5085 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname
                                                    in
                                                 let uu____5087 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name
                                                    in
                                                 let uu____5089 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   uu____5085 uu____5087
                                                   uu____5089
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____5083)
                                                in
                                             FStar_Errors.raise_error
                                               uu____5077 r
                                          in
                                       match uu____4951 with
                                       | (k,g_k) ->
                                           ((let uu____5106 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____5106
                                             then
                                               let uu____5111 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____5111
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____5119 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____5119
                                              then
                                                let uu____5124 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____5124
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____5137 =
                                                    FStar_Ident.string_of_lid
                                                      ed.FStar_Syntax_Syntax.mname
                                                     in
                                                  let uu____5139 =
                                                    FStar_Ident.string_of_lid
                                                      act1.FStar_Syntax_Syntax.action_name
                                                     in
                                                  let uu____5141 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    uu____5137 uu____5139
                                                    uu____5141
                                                   in
                                                let repr_args t =
                                                  let uu____5162 =
                                                    let uu____5163 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5163.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5162 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,a::is) ->
                                                      let uu____5215 =
                                                        let uu____5216 =
                                                          FStar_Syntax_Subst.compress
                                                            head
                                                           in
                                                        uu____5216.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____5215 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____5225,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____5235 ->
                                                           let uu____5236 =
                                                             let uu____5242 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____5242)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5236 r)
                                                  | uu____5251 ->
                                                      let uu____5252 =
                                                        let uu____5258 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5258)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____5252 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____5268 =
                                                  let uu____5269 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____5269.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5268 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____5294 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____5294 with
                                                     | (bs1,c1) ->
                                                         let uu____5301 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____5301
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
                                                              let uu____5312
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5312))
                                                | uu____5315 ->
                                                    let uu____5316 =
                                                      let uu____5322 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____5322)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____5316 r
                                                 in
                                              (let uu____5326 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____5326
                                               then
                                                 let uu____5331 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5331
                                               else ());
                                              (let act2 =
                                                 let uu____5337 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5337 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___550_5351 =
                                                         act1  in
                                                       let uu____5352 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___550_5351.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___550_5351.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___550_5351.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5352
                                                       }
                                                     else
                                                       (let uu____5355 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5362
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5362
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5355
                                                        then
                                                          let uu___555_5367 =
                                                            act1  in
                                                          let uu____5368 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___555_5367.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___555_5367.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___555_5367.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___555_5367.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5368
                                                          }
                                                        else
                                                          (let uu____5371 =
                                                             let uu____5377 =
                                                               let uu____5379
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   ed.FStar_Syntax_Syntax.mname
                                                                  in
                                                               let uu____5381
                                                                 =
                                                                 FStar_Ident.string_of_lid
                                                                   act1.FStar_Syntax_Syntax.action_name
                                                                  in
                                                               let uu____5383
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5385
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 uu____5379
                                                                 uu____5381
                                                                 uu____5383
                                                                 uu____5385
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5377)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5371 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5410 =
                      match uu____5410 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5455 =
                        let uu____5456 = tschemes_of repr  in
                        let uu____5461 = tschemes_of return_repr  in
                        let uu____5466 = tschemes_of bind_repr  in
                        let uu____5471 = tschemes_of stronger_repr  in
                        let uu____5476 = tschemes_of if_then_else  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5456;
                          FStar_Syntax_Syntax.l_return = uu____5461;
                          FStar_Syntax_Syntax.l_bind = uu____5466;
                          FStar_Syntax_Syntax.l_subcomp = uu____5471;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5476
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5455  in
                    let uu___564_5481 = ed  in
                    let uu____5482 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___564_5481.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___564_5481.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___564_5481.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___564_5481.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5489 = signature  in
                         match uu____5489 with | (us,t,uu____5504) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5482;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___564_5481.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5542 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5542
         then
           let uu____5547 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5547
         else ());
        (let uu____5553 =
           let uu____5558 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5558 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5582 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5582  in
               let uu____5583 =
                 let uu____5590 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5590 bs  in
               (match uu____5583 with
                | (bs1,uu____5596,uu____5597) ->
                    let uu____5598 =
                      let tmp_t =
                        let uu____5608 =
                          let uu____5611 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5616  ->
                                 FStar_Pervasives_Native.Some uu____5616)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5611
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5608  in
                      let uu____5617 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5617 with
                      | (us,tmp_t1) ->
                          let uu____5634 =
                            let uu____5635 =
                              let uu____5636 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5636
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5635
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5634)
                       in
                    (match uu____5598 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5673 ->
                              let uu____5676 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5683 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5683 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5676
                              then (us, bs2)
                              else
                                (let uu____5694 =
                                   let uu____5700 =
                                     let uu____5702 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname
                                        in
                                     let uu____5704 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5706 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5702 uu____5704 uu____5706
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5700)
                                    in
                                 let uu____5710 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5694
                                   uu____5710))))
            in
         match uu____5553 with
         | (us,bs) ->
             let ed1 =
               let uu___598_5718 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___598_5718.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___598_5718.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___598_5718.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___598_5718.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___598_5718.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___598_5718.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5719 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5719 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5738 =
                    let uu____5743 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5743  in
                  (match uu____5738 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5764 =
                           match uu____5764 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5784 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5784 t  in
                               let uu____5793 =
                                 let uu____5794 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5794 t1  in
                               (us1, uu____5793)
                            in
                         let uu___612_5799 = ed1  in
                         let uu____5800 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5801 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5802 =
                           FStar_List.map
                             (fun a  ->
                                let uu___615_5810 = a  in
                                let uu____5811 =
                                  let uu____5812 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5812  in
                                let uu____5823 =
                                  let uu____5824 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5824  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___615_5810.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___615_5810.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___615_5810.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___615_5810.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5811;
                                  FStar_Syntax_Syntax.action_typ = uu____5823
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___612_5799.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___612_5799.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___612_5799.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___612_5799.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5800;
                           FStar_Syntax_Syntax.combinators = uu____5801;
                           FStar_Syntax_Syntax.actions = uu____5802;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___612_5799.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5836 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5836
                         then
                           let uu____5841 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5841
                         else ());
                        (let env =
                           let uu____5848 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5848
                             ed_bs
                            in
                         let check_and_gen' comb n env_opt uu____5883 k =
                           match uu____5883 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5903 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5903 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5912 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5912 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5913 =
                                            let uu____5920 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5920 t1
                                             in
                                          (match uu____5913 with
                                           | (t2,uu____5922,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5925 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5925 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5941 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname
                                                  in
                                               let uu____5943 =
                                                 FStar_Util.string_of_int n
                                                  in
                                               let uu____5945 =
                                                 let uu____5947 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5947
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5941 comb uu____5943
                                                 uu____5945
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5962 ->
                                               let uu____5963 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5970 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5970 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5963
                                               then (g_us, t3)
                                               else
                                                 (let uu____5981 =
                                                    let uu____5987 =
                                                      let uu____5989 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname
                                                         in
                                                      let uu____5991 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5993 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5989 comb
                                                        uu____5991 uu____5993
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5987)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5981
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____6001 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____6001
                          then
                            let uu____6006 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____6006
                          else ());
                         (let fresh_a_and_wp uu____6022 =
                            let fail t =
                              let uu____6035 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____6035
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____6051 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____6051 with
                            | (uu____6062,signature1) ->
                                let uu____6064 =
                                  let uu____6065 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____6065.FStar_Syntax_Syntax.n  in
                                (match uu____6064 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____6075) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____6104)::(wp,uu____6106)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6135 -> fail signature1)
                                 | uu____6136 -> fail signature1)
                             in
                          let log_combinator s ts =
                            let uu____6150 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____6150
                            then
                              let uu____6155 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname
                                 in
                              let uu____6157 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____6155 s uu____6157
                            else ()  in
                          let ret_wp =
                            let uu____6163 = fresh_a_and_wp ()  in
                            match uu____6163 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____6179 =
                                    let uu____6188 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____6195 =
                                      let uu____6204 =
                                        let uu____6211 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6211
                                         in
                                      [uu____6204]  in
                                    uu____6188 :: uu____6195  in
                                  let uu____6230 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____6179
                                    uu____6230
                                   in
                                let uu____6233 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6233
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6247 = fresh_a_and_wp ()  in
                             match uu____6247 with
                             | (a,wp_sort_a) ->
                                 let uu____6260 = fresh_a_and_wp ()  in
                                 (match uu____6260 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6276 =
                                          let uu____6285 =
                                            let uu____6292 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6292
                                             in
                                          [uu____6285]  in
                                        let uu____6305 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6276
                                          uu____6305
                                         in
                                      let k =
                                        let uu____6311 =
                                          let uu____6320 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6327 =
                                            let uu____6336 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6343 =
                                              let uu____6352 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6359 =
                                                let uu____6368 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6375 =
                                                  let uu____6384 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6384]  in
                                                uu____6368 :: uu____6375  in
                                              uu____6352 :: uu____6359  in
                                            uu____6336 :: uu____6343  in
                                          uu____6320 :: uu____6327  in
                                        let uu____6427 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6311
                                          uu____6427
                                         in
                                      let uu____6430 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6430
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6444 = fresh_a_and_wp ()  in
                              match uu____6444 with
                              | (a,wp_sort_a) ->
                                  let uu____6457 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6457 with
                                   | (t,uu____6463) ->
                                       let k =
                                         let uu____6467 =
                                           let uu____6476 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6483 =
                                             let uu____6492 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6499 =
                                               let uu____6508 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6508]  in
                                             uu____6492 :: uu____6499  in
                                           uu____6476 :: uu____6483  in
                                         let uu____6539 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6467
                                           uu____6539
                                          in
                                       let uu____6542 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6542
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6556 = fresh_a_and_wp ()  in
                               match uu____6556 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6570 =
                                       let uu____6573 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6573
                                        in
                                     let uu____6574 =
                                       let uu____6575 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6575
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6570
                                       uu____6574
                                      in
                                   let k =
                                     let uu____6587 =
                                       let uu____6596 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6603 =
                                         let uu____6612 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6619 =
                                           let uu____6628 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6635 =
                                             let uu____6644 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6644]  in
                                           uu____6628 :: uu____6635  in
                                         uu____6612 :: uu____6619  in
                                       uu____6596 :: uu____6603  in
                                     let uu____6681 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6587
                                       uu____6681
                                      in
                                   let uu____6684 =
                                     let uu____6689 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6689
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6684
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6721 = fresh_a_and_wp ()  in
                                match uu____6721 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6737 =
                                        let uu____6746 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6753 =
                                          let uu____6762 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6762]  in
                                        uu____6746 :: uu____6753  in
                                      let uu____6787 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6737
                                        uu____6787
                                       in
                                    let uu____6790 =
                                      let uu____6795 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6795
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6790
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6811 = fresh_a_and_wp ()  in
                                 match uu____6811 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6825 =
                                         let uu____6828 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6828
                                          in
                                       let uu____6829 =
                                         let uu____6830 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6830
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6825
                                         uu____6829
                                        in
                                     let wp_sort_b_a =
                                       let uu____6842 =
                                         let uu____6851 =
                                           let uu____6858 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6858
                                            in
                                         [uu____6851]  in
                                       let uu____6871 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6842
                                         uu____6871
                                        in
                                     let k =
                                       let uu____6877 =
                                         let uu____6886 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6893 =
                                           let uu____6902 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6909 =
                                             let uu____6918 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6918]  in
                                           uu____6902 :: uu____6909  in
                                         uu____6886 :: uu____6893  in
                                       let uu____6949 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6877
                                         uu____6949
                                        in
                                     let uu____6952 =
                                       let uu____6957 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6957
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6952
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6973 = fresh_a_and_wp ()  in
                                  match uu____6973 with
                                  | (a,wp_sort_a) ->
                                      let uu____6986 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6986 with
                                       | (t,uu____6992) ->
                                           let k =
                                             let uu____6996 =
                                               let uu____7005 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____7012 =
                                                 let uu____7021 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____7021]  in
                                               uu____7005 :: uu____7012  in
                                             let uu____7046 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6996 uu____7046
                                              in
                                           let trivial =
                                             let uu____7050 =
                                               let uu____7055 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7055 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____7050
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____7070 =
                                  let uu____7087 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____7087 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____7116 ->
                                      let repr =
                                        let uu____7120 = fresh_a_and_wp ()
                                           in
                                        match uu____7120 with
                                        | (a,wp_sort_a) ->
                                            let uu____7133 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____7133 with
                                             | (t,uu____7139) ->
                                                 let k =
                                                   let uu____7143 =
                                                     let uu____7152 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____7159 =
                                                       let uu____7168 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____7168]  in
                                                     uu____7152 :: uu____7159
                                                      in
                                                   let uu____7193 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7143 uu____7193
                                                    in
                                                 let uu____7196 =
                                                   let uu____7201 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7201
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7196
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7245 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____7245 with
                                          | (uu____7252,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____7255 =
                                                let uu____7262 =
                                                  let uu____7263 =
                                                    let uu____7280 =
                                                      let uu____7291 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7308 =
                                                        let uu____7319 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7319]  in
                                                      uu____7291 ::
                                                        uu____7308
                                                       in
                                                    (repr2, uu____7280)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____7263
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____7262
                                                 in
                                              uu____7255
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7385 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7385 wp  in
                                        let destruct_repr t =
                                          let uu____7400 =
                                            let uu____7401 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7401.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7400 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7412,(t1,uu____7414)::
                                               (wp,uu____7416)::[])
                                              -> (t1, wp)
                                          | uu____7475 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7491 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7491
                                              FStar_Util.must
                                             in
                                          let uu____7518 = fresh_a_and_wp ()
                                             in
                                          match uu____7518 with
                                          | (a,uu____7526) ->
                                              let x_a =
                                                let uu____7532 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7532
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7540 =
                                                    let uu____7545 =
                                                      let uu____7546 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7546
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7555 =
                                                      let uu____7556 =
                                                        let uu____7565 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7565
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7574 =
                                                        let uu____7585 =
                                                          let uu____7594 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7594
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7585]  in
                                                      uu____7556 ::
                                                        uu____7574
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7545 uu____7555
                                                     in
                                                  uu____7540
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7630 =
                                                  let uu____7639 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7646 =
                                                    let uu____7655 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7655]  in
                                                  uu____7639 :: uu____7646
                                                   in
                                                let uu____7680 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7630 uu____7680
                                                 in
                                              let uu____7683 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7683 with
                                               | (k1,uu____7691,uu____7692)
                                                   ->
                                                   let env1 =
                                                     let uu____7696 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7696
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
                                             let uu____7709 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7709
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7747 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7747
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7748 = fresh_a_and_wp ()
                                              in
                                           match uu____7748 with
                                           | (a,wp_sort_a) ->
                                               let uu____7761 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7761 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7777 =
                                                        let uu____7786 =
                                                          let uu____7793 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7793
                                                           in
                                                        [uu____7786]  in
                                                      let uu____7806 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7777 uu____7806
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
                                                      let uu____7814 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7814
                                                       in
                                                    let wp_g_x =
                                                      let uu____7819 =
                                                        let uu____7824 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7825 =
                                                          let uu____7826 =
                                                            let uu____7835 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7835
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7826]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7824
                                                          uu____7825
                                                         in
                                                      uu____7819
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7866 =
                                                          let uu____7871 =
                                                            let uu____7872 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7872
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7881 =
                                                            let uu____7882 =
                                                              let uu____7885
                                                                =
                                                                let uu____7888
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7889
                                                                  =
                                                                  let uu____7892
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7893
                                                                    =
                                                                    let uu____7896
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7897
                                                                    =
                                                                    let uu____7900
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7900]
                                                                     in
                                                                    uu____7896
                                                                    ::
                                                                    uu____7897
                                                                     in
                                                                  uu____7892
                                                                    ::
                                                                    uu____7893
                                                                   in
                                                                uu____7888 ::
                                                                  uu____7889
                                                                 in
                                                              r :: uu____7885
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7882
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7871
                                                            uu____7881
                                                           in
                                                        uu____7866
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7918 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7918
                                                      then
                                                        let uu____7929 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7936 =
                                                          let uu____7945 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7945]  in
                                                        uu____7929 ::
                                                          uu____7936
                                                      else []  in
                                                    let k =
                                                      let uu____7981 =
                                                        let uu____7990 =
                                                          let uu____7999 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____8006 =
                                                            let uu____8015 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____8015]  in
                                                          uu____7999 ::
                                                            uu____8006
                                                           in
                                                        let uu____8040 =
                                                          let uu____8049 =
                                                            let uu____8058 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____8065 =
                                                              let uu____8074
                                                                =
                                                                let uu____8081
                                                                  =
                                                                  let uu____8082
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____8082
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____8081
                                                                 in
                                                              let uu____8083
                                                                =
                                                                let uu____8092
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____8099
                                                                  =
                                                                  let uu____8108
                                                                    =
                                                                    let uu____8115
                                                                    =
                                                                    let uu____8116
                                                                    =
                                                                    let uu____8125
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____8125]
                                                                     in
                                                                    let uu____8144
                                                                    =
                                                                    let uu____8147
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____8147
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____8116
                                                                    uu____8144
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____8115
                                                                     in
                                                                  [uu____8108]
                                                                   in
                                                                uu____8092 ::
                                                                  uu____8099
                                                                 in
                                                              uu____8074 ::
                                                                uu____8083
                                                               in
                                                            uu____8058 ::
                                                              uu____8065
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____8049
                                                           in
                                                        FStar_List.append
                                                          uu____7990
                                                          uu____8040
                                                         in
                                                      let uu____8192 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7981 uu____8192
                                                       in
                                                    let uu____8195 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____8195 with
                                                     | (k1,uu____8203,uu____8204)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___810_8214
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___810_8214.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun uu____8216 
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8216)
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
                                              (let uu____8243 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8257 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____8257 with
                                                    | (usubst,uvs) ->
                                                        let uu____8280 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____8281 =
                                                          let uu___823_8282 =
                                                            act  in
                                                          let uu____8283 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____8284 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___823_8282.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___823_8282.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___823_8282.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8283;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8284
                                                          }  in
                                                        (uu____8280,
                                                          uu____8281))
                                                  in
                                               match uu____8243 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____8288 =
                                                       let uu____8289 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____8289.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____8288 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____8315 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____8315
                                                         then
                                                           let uu____8318 =
                                                             let uu____8321 =
                                                               let uu____8322
                                                                 =
                                                                 let uu____8323
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8323
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8322
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8321
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8318
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8346 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8347 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8347 with
                                                    | (act_typ1,uu____8355,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___840_8358 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___840_8358.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____8361 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8361
                                                          then
                                                            let uu____8365 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8367 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8369 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8365
                                                              uu____8367
                                                              uu____8369
                                                          else ());
                                                         (let uu____8374 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8374
                                                          with
                                                          | (act_defn,uu____8382,g_a)
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
                                                              let uu____8386
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
                                                                    let uu____8422
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8422
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8434)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8441
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8441
                                                                     in
                                                                    let uu____8444
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8444
                                                                    with
                                                                    | 
                                                                    (k1,uu____8458,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8462
                                                                    ->
                                                                    let uu____8463
                                                                    =
                                                                    let uu____8469
                                                                    =
                                                                    let uu____8471
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8473
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8471
                                                                    uu____8473
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8469)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8463
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8386
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
                                                                    let uu____8491
                                                                    =
                                                                    let uu____8492
                                                                    =
                                                                    let uu____8493
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8493
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8492
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8491);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8495
                                                                    =
                                                                    let uu____8496
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8496.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8495
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8521
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8521
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8528
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8528
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8548
                                                                    =
                                                                    let uu____8549
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8549]
                                                                     in
                                                                    let uu____8550
                                                                    =
                                                                    let uu____8561
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8561]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8548;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8550;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8586
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8586))
                                                                    | 
                                                                    uu____8589
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8591
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8613
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8613))
                                                                     in
                                                                    match uu____8591
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
                                                                    let uu___890_8632
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___890_8632.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___890_8632.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___890_8632.FStar_Syntax_Syntax.action_params);
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
                                match uu____7070 with
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
                                      let uu____8675 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8675 ts1
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
                                          uu____8687 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8688 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8689 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___910_8692 = ed2  in
                                      let uu____8693 = cl signature  in
                                      let uu____8694 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___913_8702 = a  in
                                             let uu____8703 =
                                               let uu____8704 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8704
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8729 =
                                               let uu____8730 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8730
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___913_8702.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___913_8702.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___913_8702.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___913_8702.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8703;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8729
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___910_8692.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___910_8692.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___910_8692.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___910_8692.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8693;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8694;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___910_8692.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8756 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8756
                                      then
                                        let uu____8761 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8761
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
        let uu____8787 =
          let uu____8802 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8802 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8787 env ed quals
  
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
        let fail uu____8852 =
          let uu____8853 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8859 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8853 uu____8859  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8903)::(wp,uu____8905)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8934 -> fail ())
        | uu____8935 -> fail ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub  ->
      (let uu____8948 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8948
       then
         let uu____8953 = FStar_Syntax_Print.sub_eff_to_string sub  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8953
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8970 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8970.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.target
           in
        let uu____8982 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8986 =
                let uu____8987 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8987 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8986
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8996 =
                   let uu____8997 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8997 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8996
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____9005 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____9005))
           in
        if uu____8982
        then
          let uu____9008 =
            let uu____9014 =
              let uu____9016 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____9019 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____9016 uu____9019
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____9014)  in
          FStar_Errors.raise_error uu____9008 r
        else ());
       (let uu____9026 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____9026 with
        | (us,lift,lift_ty) ->
            ((let uu____9040 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____9040
              then
                let uu____9045 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____9051 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____9045 uu____9051
              else ());
             (let uu____9060 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____9060 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____9078 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.source
                         in
                      let uu____9080 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.target
                         in
                      let uu____9082 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____9078 uu____9080 s uu____9082
                       in
                    let uu____9085 =
                      let uu____9092 =
                        let uu____9097 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____9097
                          (fun uu____9114  ->
                             match uu____9114 with
                             | (t,u) ->
                                 let uu____9125 =
                                   let uu____9126 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____9126
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____9125, u))
                         in
                      match uu____9092 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____9145 =
                              let uu____9146 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____9146.FStar_Syntax_Syntax.n  in
                            match uu____9145 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____9158)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____9186 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____9186 with
                                 | (a',uu____9196)::bs1 ->
                                     let uu____9216 =
                                       let uu____9217 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____9217
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____9283 =
                                       let uu____9296 =
                                         let uu____9299 =
                                           let uu____9300 =
                                             let uu____9307 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____9307)  in
                                           FStar_Syntax_Syntax.NT uu____9300
                                            in
                                         [uu____9299]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____9296
                                        in
                                     FStar_All.pipe_right uu____9216
                                       uu____9283)
                            | uu____9322 ->
                                let uu____9323 =
                                  let uu____9329 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____9329)
                                   in
                                FStar_Errors.raise_error uu____9323 r
                             in
                          let uu____9341 =
                            let uu____9352 =
                              let uu____9357 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9364 =
                                let uu____9365 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9365
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9357 r sub.FStar_Syntax_Syntax.source
                                u_a uu____9364
                               in
                            match uu____9352 with
                            | (f_sort,g) ->
                                let uu____9386 =
                                  let uu____9393 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9393
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9386, g)
                             in
                          (match uu____9341 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9460 =
                                 let uu____9465 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9466 =
                                   let uu____9467 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9467
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9465 r
                                   sub.FStar_Syntax_Syntax.target u_a
                                   uu____9466
                                  in
                               (match uu____9460 with
                                | (repr,g_repr) ->
                                    let uu____9484 =
                                      let uu____9489 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9490 =
                                        let uu____9492 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9494 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9492 uu____9494
                                         in
                                      pure_wp_uvar uu____9489 repr uu____9490
                                        r
                                       in
                                    (match uu____9484 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9506 =
                                             let uu____9507 =
                                               let uu____9508 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9508]  in
                                             let uu____9509 =
                                               let uu____9520 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9520]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9507;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9509;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9506
                                            in
                                         let uu____9553 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9556 =
                                           let uu____9557 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9557 guard_wp
                                            in
                                         (uu____9553, uu____9556))))
                       in
                    match uu____9085 with
                    | (k,g_k) ->
                        ((let uu____9567 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9567
                          then
                            let uu____9572 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9572
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9581 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9581
                           then
                             let uu____9586 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9586
                           else ());
                          (let sub1 =
                             let uu___1006_9592 = sub  in
                             let uu____9593 =
                               let uu____9596 =
                                 let uu____9597 =
                                   let uu____9600 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9600
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9597)  in
                               FStar_Pervasives_Native.Some uu____9596  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1006_9592.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1006_9592.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9593;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9612 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9612
                            then
                              let uu____9617 =
                                FStar_Syntax_Print.sub_eff_to_string sub1  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9617
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
          let uu____9654 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9654  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target
           in
        let uu____9657 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9657
        then tc_layered_lift env sub
        else
          (let uu____9664 =
             let uu____9671 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source
                in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9671
              in
           match uu____9664 with
           | (a,wp_a_src) ->
               let uu____9678 =
                 let uu____9685 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9685
                  in
               (match uu____9678 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9693 =
                        let uu____9696 =
                          let uu____9697 =
                            let uu____9704 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9704)  in
                          FStar_Syntax_Syntax.NT uu____9697  in
                        [uu____9696]  in
                      FStar_Syntax_Subst.subst uu____9693 wp_b_tgt  in
                    let expected_k =
                      let uu____9712 =
                        let uu____9721 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9728 =
                          let uu____9737 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9737]  in
                        uu____9721 :: uu____9728  in
                      let uu____9762 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9712 uu____9762  in
                    let repr_type eff_name a1 wp =
                      (let uu____9784 =
                         let uu____9786 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9786  in
                       if uu____9784
                       then
                         let uu____9789 =
                           let uu____9795 =
                             let uu____9797 =
                               FStar_Ident.string_of_lid eff_name  in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9797
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9795)
                            in
                         let uu____9801 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9789 uu____9801
                       else ());
                      (let uu____9804 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9804 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9837 =
                               let uu____9838 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9838
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9837
                              in
                           let uu____9845 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9846 =
                             let uu____9853 =
                               let uu____9854 =
                                 let uu____9871 =
                                   let uu____9882 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9891 =
                                     let uu____9902 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9902]  in
                                   uu____9882 :: uu____9891  in
                                 (repr, uu____9871)  in
                               FStar_Syntax_Syntax.Tm_app uu____9854  in
                             FStar_Syntax_Syntax.mk uu____9853  in
                           uu____9846 FStar_Pervasives_Native.None uu____9845)
                       in
                    let uu____9947 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____10120 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____10131 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____10131 with
                              | (usubst,uvs1) ->
                                  let uu____10154 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____10155 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____10154, uu____10155)
                            else (env, lift_wp)  in
                          (match uu____10120 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10205 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10205))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10276 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10291 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10291 with
                              | (usubst,uvs) ->
                                  let uu____10316 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10316)
                            else ([], lift)  in
                          (match uu____10276 with
                           | (uvs,lift1) ->
                               ((let uu____10352 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10352
                                 then
                                   let uu____10356 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10356
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10362 =
                                   let uu____10369 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10369 lift1
                                    in
                                 match uu____10362 with
                                 | (lift2,comp,uu____10394) ->
                                     let uu____10395 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10395 with
                                      | (uu____10424,lift_wp,lift_elab) ->
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
                                            let uu____10456 =
                                              let uu____10467 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10467
                                               in
                                            let uu____10484 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10456, uu____10484)
                                          else
                                            (let uu____10513 =
                                               let uu____10524 =
                                                 let uu____10533 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10533)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10524
                                                in
                                             let uu____10548 =
                                               let uu____10557 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10557)  in
                                             (uu____10513, uu____10548))))))
                       in
                    (match uu____9947 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1090_10621 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1090_10621.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1090_10621.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1090_10621.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1090_10621.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1090_10621.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1090_10621.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1090_10621.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1090_10621.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1090_10621.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1090_10621.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1090_10621.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1090_10621.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1090_10621.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1090_10621.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1090_10621.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1090_10621.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1090_10621.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1090_10621.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1090_10621.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1090_10621.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1090_10621.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1090_10621.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1090_10621.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1090_10621.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1090_10621.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1090_10621.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1090_10621.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1090_10621.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1090_10621.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1090_10621.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1090_10621.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1090_10621.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1090_10621.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1090_10621.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1090_10621.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1090_10621.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1090_10621.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1090_10621.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1090_10621.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1090_10621.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1090_10621.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1090_10621.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1090_10621.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1090_10621.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1090_10621.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10654 =
                                 let uu____10659 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10659 with
                                 | (usubst,uvs1) ->
                                     let uu____10682 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10683 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10682, uu____10683)
                                  in
                               (match uu____10654 with
                                | (env2,lift2) ->
                                    let uu____10688 =
                                      let uu____10695 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10695
                                       in
                                    (match uu____10688 with
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
                                             let uu____10721 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10722 =
                                               let uu____10729 =
                                                 let uu____10730 =
                                                   let uu____10747 =
                                                     let uu____10758 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10767 =
                                                       let uu____10778 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10778]  in
                                                     uu____10758 ::
                                                       uu____10767
                                                      in
                                                   (lift_wp1, uu____10747)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10730
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10729
                                                in
                                             uu____10722
                                               FStar_Pervasives_Native.None
                                               uu____10721
                                              in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10826 =
                                             let uu____10835 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10842 =
                                               let uu____10851 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10858 =
                                                 let uu____10867 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10867]  in
                                               uu____10851 :: uu____10858  in
                                             uu____10835 :: uu____10842  in
                                           let uu____10898 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10826 uu____10898
                                            in
                                         let uu____10901 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10901 with
                                          | (expected_k2,uu____10911,uu____10912)
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
                                                   let uu____10920 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10920))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10928 =
                             let uu____10930 =
                               let uu____10932 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10932
                                 FStar_List.length
                                in
                             uu____10930 <> Prims.int_one  in
                           if uu____10928
                           then
                             let uu____10955 =
                               let uu____10961 =
                                 let uu____10963 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10965 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10967 =
                                   let uu____10969 =
                                     let uu____10971 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10971
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10969
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10963 uu____10965 uu____10967
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10961)
                                in
                             FStar_Errors.raise_error uu____10955 r
                           else ());
                          (let uu____10998 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____11001 =
                                  let uu____11003 =
                                    let uu____11006 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____11006
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____11003
                                    FStar_List.length
                                   in
                                uu____11001 <> Prims.int_one)
                              in
                           if uu____10998
                           then
                             let uu____11045 =
                               let uu____11051 =
                                 let uu____11053 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____11055 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____11057 =
                                   let uu____11059 =
                                     let uu____11061 =
                                       let uu____11064 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____11064
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____11061
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____11059
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____11053 uu____11055 uu____11057
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____11051)
                                in
                             FStar_Errors.raise_error uu____11045 r
                           else ());
                          (let uu___1127_11106 = sub  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1127_11106.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1127_11106.FStar_Syntax_Syntax.target);
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
    fun uu____11137  ->
      fun r  ->
        match uu____11137 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____11160 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11188 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11188 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11219 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11219 c  in
                     let uu____11228 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11228, uvs1, tps1, c1))
               in
            (match uu____11160 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11248 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11248 with
                  | (tps2,c2) ->
                      let uu____11263 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11263 with
                       | (tps3,env3,us) ->
                           let uu____11281 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11281 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11307)::uu____11308 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11327 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11335 =
                                    let uu____11337 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11337  in
                                  if uu____11335
                                  then
                                    let uu____11340 =
                                      let uu____11346 =
                                        let uu____11348 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11350 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11348 uu____11350
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11346)
                                       in
                                    FStar_Errors.raise_error uu____11340 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11358 =
                                    let uu____11359 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11359
                                     in
                                  match uu____11358 with
                                  | (uvs2,t) ->
                                      let uu____11388 =
                                        let uu____11393 =
                                          let uu____11406 =
                                            let uu____11407 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11407.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11406)  in
                                        match uu____11393 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11422,c5)) -> ([], c5)
                                        | (uu____11464,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11503 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11388 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11535 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11535 with
                                               | (uu____11540,t1) ->
                                                   let uu____11542 =
                                                     let uu____11548 =
                                                       let uu____11550 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11552 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11556 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11550
                                                         uu____11552
                                                         uu____11556
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11548)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11542 r)
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
              let uu____11598 = FStar_Ident.string_of_lid m  in
              let uu____11600 = FStar_Ident.string_of_lid n  in
              let uu____11602 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11598 uu____11600
                uu____11602
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11610 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11610 with
            | (us,t,ty) ->
                let uu____11626 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11626 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11639 =
                         let uu____11644 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11644
                           (fun uu____11661  ->
                              match uu____11661 with
                              | (t1,u) ->
                                  let uu____11672 =
                                    let uu____11673 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11673
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11672, u))
                          in
                       match uu____11639 with
                       | (a,u_a) ->
                           let uu____11681 =
                             let uu____11686 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11686
                               (fun uu____11703  ->
                                  match uu____11703 with
                                  | (t1,u) ->
                                      let uu____11714 =
                                        let uu____11715 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11715
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11714, u))
                              in
                           (match uu____11681 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11732 =
                                    let uu____11733 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11733.FStar_Syntax_Syntax.n  in
                                  match uu____11732 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11745) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11773 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11773 with
                                       | (a',uu____11783)::(b',uu____11785)::bs1
                                           ->
                                           let uu____11815 =
                                             let uu____11816 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11816
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11882 =
                                             let uu____11895 =
                                               let uu____11898 =
                                                 let uu____11899 =
                                                   let uu____11906 =
                                                     let uu____11909 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11909
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11906)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11899
                                                  in
                                               let uu____11922 =
                                                 let uu____11925 =
                                                   let uu____11926 =
                                                     let uu____11933 =
                                                       let uu____11936 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11936
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11933)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11926
                                                    in
                                                 [uu____11925]  in
                                               uu____11898 :: uu____11922  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11895
                                              in
                                           FStar_All.pipe_right uu____11815
                                             uu____11882)
                                  | uu____11957 ->
                                      let uu____11958 =
                                        let uu____11964 =
                                          let uu____11966 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11968 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11966 uu____11968
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11964)
                                         in
                                      FStar_Errors.raise_error uu____11958 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____12001 =
                                  let uu____12012 =
                                    let uu____12017 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____12018 =
                                      let uu____12019 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____12019
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____12017 r m u_a uu____12018
                                     in
                                  match uu____12012 with
                                  | (repr,g) ->
                                      let uu____12040 =
                                        let uu____12047 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____12047
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____12040, g)
                                   in
                                (match uu____12001 with
                                 | (f,guard_f) ->
                                     let uu____12079 =
                                       let x_a =
                                         let uu____12097 =
                                           let uu____12098 =
                                             let uu____12099 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____12099
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____12098
                                            in
                                         FStar_All.pipe_right uu____12097
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____12115 =
                                         let uu____12120 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____12139 =
                                           let uu____12140 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____12140
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____12120 r n u_b uu____12139
                                          in
                                       match uu____12115 with
                                       | (repr,g) ->
                                           let uu____12161 =
                                             let uu____12168 =
                                               let uu____12169 =
                                                 let uu____12170 =
                                                   let uu____12173 =
                                                     let uu____12176 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12176
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12173
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12170
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12169
                                                in
                                             FStar_All.pipe_right uu____12168
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____12161, g)
                                        in
                                     (match uu____12079 with
                                      | (g,guard_g) ->
                                          let uu____12220 =
                                            let uu____12225 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____12226 =
                                              let uu____12227 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____12227
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12225 r p u_b uu____12226
                                             in
                                          (match uu____12220 with
                                           | (repr,guard_repr) ->
                                               let uu____12242 =
                                                 let uu____12247 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____12248 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____12247
                                                   repr uu____12248 r
                                                  in
                                               (match uu____12242 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____12260 =
                                                        let uu____12263 =
                                                          let uu____12264 =
                                                            let uu____12265 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____12265]  in
                                                          let uu____12266 =
                                                            let uu____12277 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____12277]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12264;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12266;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12263
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12260
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
                                                     (let uu____12337 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____12337
                                                      then
                                                        let uu____12341 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____12347 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12341
                                                          uu____12347
                                                      else ());
                                                     (let uu____12357 =
                                                        let uu____12363 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12363)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12357);
                                                     (let uu____12367 =
                                                        let uu____12368 =
                                                          let uu____12371 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12371
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12368)
                                                         in
                                                      ((us1, t), uu____12367)))))))))))
  