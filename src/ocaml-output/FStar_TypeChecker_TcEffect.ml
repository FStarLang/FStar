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
        fun n1  ->
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
                               (if (FStar_List.length g_us) <> n1
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n1  in
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
             FStar_TypeChecker_Env.is_native_tactic =
               (uu___54_349.FStar_TypeChecker_Env.is_native_tactic);
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
               (uu___54_349.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___54_349.FStar_TypeChecker_Env.enable_defer_to_tac)
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
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____402)
        else ();
        (let log_combinator s uu____431 =
           match uu____431 with
           | (us,t,ty) ->
               let uu____460 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____460
               then
                 let uu____465 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____471 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____465
                   uu____471
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____496 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____496
             (fun uu____513  ->
                match uu____513 with
                | (t,u) ->
                    let uu____524 =
                      let uu____525 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____525
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____524, u))
            in
         let fresh_x_a x a =
           let uu____539 =
             let uu____540 =
               let uu____541 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____541 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____540
              in
           FStar_All.pipe_right uu____539 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           check_and_gen env0 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
            in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____593 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____593 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____617 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____617 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____637 = fresh_a_and_u_a "a"  in
                    (match uu____637 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____658 =
                             let uu____659 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____659
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____658
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____690 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____690  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____695 =
                             let uu____698 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____698
                              in
                           (sig_us, uu____695, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____707 =
            let repr_ts =
              let uu____729 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____729 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____757 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____757 with
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
                  let uu____788 =
                    let uu____789 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____789.FStar_Syntax_Syntax.n  in
                  match uu____788 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____792,t,uu____794) ->
                      let uu____819 =
                        let uu____820 = FStar_Syntax_Subst.compress t  in
                        uu____820.FStar_Syntax_Syntax.n  in
                      (match uu____819 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____823,c) ->
                           let uu____845 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____845
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____848 ->
                           let uu____849 =
                             let uu____855 =
                               let uu____857 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____860 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____857 uu____860
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____855)
                              in
                           FStar_Errors.raise_error uu____849 r)
                  | uu____864 ->
                      let uu____865 =
                        let uu____871 =
                          let uu____873 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____876 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____873 uu____876
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____871)  in
                      FStar_Errors.raise_error uu____865 r
                   in
                ((let uu____881 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____887 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____887)
                     in
                  if uu____881
                  then
                    let uu____890 =
                      let uu____896 =
                        let uu____898 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____901 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____898 uu____901
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____896)
                       in
                    FStar_Errors.raise_error uu____890 r
                  else ());
                 (let uu____908 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____908 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____932 = fresh_a_and_u_a "a"  in
                      (match uu____932 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____958 = signature  in
                               match uu____958 with
                               | (us1,t,uu____973) -> (us1, t)  in
                             let uu____990 =
                               let uu____991 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____991
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____990
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1018 =
                               let uu____1021 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1021
                                 (fun uu____1034  ->
                                    match uu____1034 with
                                    | (t,u1) ->
                                        let uu____1041 =
                                          let uu____1044 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1044
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1041)
                                in
                             FStar_Syntax_Util.arrow bs uu____1018  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1047 =
                               let uu____1060 =
                                 let uu____1063 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1063
                                  in
                               (repr_us, repr_t, uu____1060)  in
                             (uu____1047, underlying_effect_lid))))))
             in
          match uu____707 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1136 = signature  in
                    match uu____1136 with | (us,t,uu____1151) -> (us, t)  in
                  let repr_ts =
                    let uu____1169 = repr  in
                    match uu____1169 with | (us,t,uu____1184) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1234 =
                    let uu____1240 =
                      let uu____1242 = FStar_Util.string_of_int n1  in
                      let uu____1244 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1246 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1242 uu____1244 uu____1246
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1240)  in
                  FStar_Errors.raise_error uu____1234 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1276 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1276 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1304 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1304 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1328 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1328 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1349 = fresh_a_and_u_a "a"  in
                             match uu____1349 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1380 =
                                     let uu____1381 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1381.FStar_Syntax_Syntax.n  in
                                   match uu____1380 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1393) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1421 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1421 with
                                        | (a',uu____1431)::(x',uu____1433)::bs1
                                            ->
                                            let uu____1463 =
                                              let uu____1464 =
                                                let uu____1469 =
                                                  let uu____1472 =
                                                    let uu____1473 =
                                                      let uu____1480 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1480)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1473
                                                     in
                                                  [uu____1472]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1469
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1464
                                               in
                                            let uu____1487 =
                                              let uu____1500 =
                                                let uu____1503 =
                                                  let uu____1504 =
                                                    let uu____1511 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1511)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1504
                                                   in
                                                [uu____1503]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1500
                                               in
                                            FStar_All.pipe_right uu____1463
                                              uu____1487)
                                   | uu____1526 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1550 =
                                   let uu____1555 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1556 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1555 u_a uu____1556  in
                                 (match uu____1550 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1576 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1576
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1581 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1581);
                                       (let uu____1582 =
                                          let uu____1585 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1585
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1582)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1614 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1614 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1626 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1626 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1650 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1650 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1671 = fresh_a_and_u_a "a"  in
                              match uu____1671 with
                              | (a,u_a) ->
                                  let uu____1691 = fresh_a_and_u_a "b"  in
                                  (match uu____1691 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1720 =
                                           let uu____1721 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1721.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1720 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1733) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1761 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1761 with
                                              | (a',uu____1771)::(b',uu____1773)::bs1
                                                  ->
                                                  let uu____1803 =
                                                    let uu____1804 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1804
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1902 =
                                                    let uu____1915 =
                                                      let uu____1918 =
                                                        let uu____1919 =
                                                          let uu____1926 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1926)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1919
                                                         in
                                                      let uu____1933 =
                                                        let uu____1936 =
                                                          let uu____1937 =
                                                            let uu____1944 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1944)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1937
                                                           in
                                                        [uu____1936]  in
                                                      uu____1918 ::
                                                        uu____1933
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1915
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1803 uu____1902)
                                         | uu____1959 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1983 =
                                         let uu____1994 =
                                           let uu____1999 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2000 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1999 u_a
                                             uu____2000
                                            in
                                         match uu____1994 with
                                         | (repr1,g) ->
                                             let uu____2015 =
                                               let uu____2022 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2022
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2015, g)
                                          in
                                       (match uu____1983 with
                                        | (f,guard_f) ->
                                            let uu____2062 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2075 =
                                                let uu____2080 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2099 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2080 u_b
                                                  uu____2099
                                                 in
                                              match uu____2075 with
                                              | (repr1,g) ->
                                                  let uu____2114 =
                                                    let uu____2121 =
                                                      let uu____2122 =
                                                        let uu____2123 =
                                                          let uu____2126 =
                                                            let uu____2129 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2129
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2126
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2123
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2122
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2121
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2114, g)
                                               in
                                            (match uu____2062 with
                                             | (g,guard_g) ->
                                                 let uu____2181 =
                                                   let uu____2186 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2187 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2186
                                                     u_b uu____2187
                                                    in
                                                 (match uu____2181 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2204 =
                                                        let uu____2209 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2210 =
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                           in
                                                        pure_wp_uvar
                                                          uu____2209 repr1
                                                          uu____2210 r
                                                         in
                                                      (match uu____2204 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2230 =
                                                               let uu____2233
                                                                 =
                                                                 let uu____2234
                                                                   =
                                                                   let uu____2235
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2235]
                                                                    in
                                                                 let uu____2236
                                                                   =
                                                                   let uu____2247
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2247]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2234;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2236;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2233
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2230
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
                                                            (let uu____2306 =
                                                               let uu____2309
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2309
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2306)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2338 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2338 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2366 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2366 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2391 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2391
                          then
                            let uu____2396 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2402 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2396 uu____2402
                          else ());
                         (let uu____2411 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2411 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2432 = fresh_a_and_u_a "a"  in
                                match uu____2432 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2461 =
                                        let uu____2462 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2462.FStar_Syntax_Syntax.n  in
                                      match uu____2461 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2474) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2502 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2502 with
                                           | (a',uu____2512)::bs1 ->
                                               let uu____2532 =
                                                 let uu____2533 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2533
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2599 =
                                                 let uu____2612 =
                                                   let uu____2615 =
                                                     let uu____2616 =
                                                       let uu____2623 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2623)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2616
                                                      in
                                                   [uu____2615]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2612
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2532 uu____2599)
                                      | uu____2638 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2656 =
                                      let uu____2667 =
                                        let uu____2672 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2673 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2672 u uu____2673
                                         in
                                      match uu____2667 with
                                      | (repr1,g) ->
                                          let uu____2688 =
                                            let uu____2695 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2695
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2688, g)
                                       in
                                    (match uu____2656 with
                                     | (f,guard_f) ->
                                         let uu____2735 =
                                           let uu____2740 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2741 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2740 u
                                             uu____2741
                                            in
                                         (match uu____2735 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2758 =
                                                let uu____2763 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2764 =
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   in
                                                pure_wp_uvar uu____2763 ret_t
                                                  uu____2764 r
                                                 in
                                              (match uu____2758 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2782 =
                                                       let uu____2783 =
                                                         let uu____2784 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2784]  in
                                                       let uu____2785 =
                                                         let uu____2796 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2796]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2783;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2785;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2782
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2851 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2851
                                                     then
                                                       let uu____2856 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2856
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
                                                     (let uu____2863 =
                                                        let uu____2866 =
                                                          let uu____2867 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2867
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2866
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2863)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2898 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2898 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2914 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2914 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2938 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2938 with
                          | (us,t) ->
                              let uu____2957 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2957 with
                               | (uu____2974,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____2978 = fresh_a_and_u_a "a"  in
                                     match uu____2978 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3007 =
                                             let uu____3008 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3008.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3007 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3020) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3048 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3048 with
                                                | (a',uu____3058)::bs1 ->
                                                    let uu____3078 =
                                                      let uu____3079 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3079
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3177 =
                                                      let uu____3190 =
                                                        let uu____3193 =
                                                          let uu____3194 =
                                                            let uu____3201 =
                                                              let uu____3204
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3204
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3201)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3194
                                                           in
                                                        [uu____3193]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3190
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3078 uu____3177)
                                           | uu____3225 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3243 =
                                           let uu____3254 =
                                             let uu____3259 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3260 =
                                               let uu____3261 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3261
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3259 u_a
                                               uu____3260
                                              in
                                           match uu____3254 with
                                           | (repr1,g) ->
                                               let uu____3282 =
                                                 let uu____3289 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3289
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3282, g)
                                            in
                                         (match uu____3243 with
                                          | (f_bs,guard_f) ->
                                              let uu____3329 =
                                                let uu____3340 =
                                                  let uu____3345 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3346 =
                                                    let uu____3347 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3347
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3345 u_a
                                                    uu____3346
                                                   in
                                                match uu____3340 with
                                                | (repr1,g) ->
                                                    let uu____3368 =
                                                      let uu____3375 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3375
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3368, g)
                                                 in
                                              (match uu____3329 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3422 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3422
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3430 =
                                                     let uu____3435 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3454 =
                                                       let uu____3455 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3455
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3435
                                                       u_a uu____3454
                                                      in
                                                   (match uu____3430 with
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
                                                         (let uu____3515 =
                                                            let uu____3518 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3518
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3515,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3531 =
                        let uu____3534 =
                          let uu____3543 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3543 FStar_Util.must  in
                        FStar_All.pipe_right uu____3534
                          FStar_Pervasives_Native.snd
                         in
                      uu____3531.FStar_Syntax_Syntax.pos  in
                    let uu____3572 = if_then_else1  in
                    match uu____3572 with
                    | (ite_us,ite_t,uu____3587) ->
                        let uu____3600 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3600 with
                         | (us,ite_t1) ->
                             let uu____3607 =
                               let uu____3618 =
                                 let uu____3619 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3619.FStar_Syntax_Syntax.n  in
                               match uu____3618 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3633,uu____3634) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3660 =
                                     let uu____3667 =
                                       let uu____3670 =
                                         let uu____3673 =
                                           let uu____3682 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3682
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3673
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3670
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3667
                                       (fun l  ->
                                          let uu____3826 = l  in
                                          match uu____3826 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3660 with
                                    | (f,g,p) ->
                                        let uu____3851 =
                                          let uu____3852 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3852 bs1
                                           in
                                        let uu____3853 =
                                          let uu____3854 =
                                            let uu____3859 =
                                              let uu____3860 =
                                                let uu____3863 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3863
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3860
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3859
                                             in
                                          uu____3854
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3851, uu____3853, f, g, p))
                               | uu____3890 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3607 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3907 =
                                    let uu____3916 = stronger_repr  in
                                    match uu____3916 with
                                    | (uu____3937,subcomp_t,subcomp_ty) ->
                                        let uu____3952 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3952 with
                                         | (uu____3965,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3976 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3976 with
                                               | (uu____3989,subcomp_ty1) ->
                                                   let uu____3991 =
                                                     let uu____3992 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3992.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3991 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4004) ->
                                                        let uu____4025 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4025
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4131 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4149 =
                                                 let uu____4154 =
                                                   let uu____4155 =
                                                     let uu____4158 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4178 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4158 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4155
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4154
                                                  in
                                               uu____4149
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4187 = aux f_t  in
                                             let uu____4190 = aux g_t  in
                                             (uu____4187, uu____4190))
                                     in
                                  (match uu____3907 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4207 =
                                         let aux t =
                                           let uu____4224 =
                                             let uu____4231 =
                                               let uu____4232 =
                                                 let uu____4259 =
                                                   let uu____4276 =
                                                     let uu____4285 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4285
                                                      in
                                                   (uu____4276,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4259,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4232
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4231
                                              in
                                           uu____4224
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4326 = aux subcomp_f  in
                                         let uu____4327 = aux subcomp_g  in
                                         (uu____4326, uu____4327)  in
                                       (match uu____4207 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4331 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4331
                                              then
                                                let uu____4336 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4338 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4336 uu____4338
                                              else ());
                                             (let uu____4343 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4343 with
                                              | (uu____4350,uu____4351,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4354 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4354 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4356 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4356 with
                                                    | (uu____4363,uu____4364,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4370 =
                                                              let uu____4375
                                                                =
                                                                let uu____4376
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4376
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4377
                                                                =
                                                                let uu____4378
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4378]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4375
                                                                uu____4377
                                                               in
                                                            uu____4370
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4411 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4411 g_g
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
                        (let uu____4435 =
                           let uu____4441 =
                             let uu____4443 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4443
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4441)
                            in
                         FStar_Errors.raise_error uu____4435 r)
                      else ();
                      (let uu____4450 =
                         let uu____4455 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4455 with
                         | (usubst,us) ->
                             let uu____4478 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4479 =
                               let uu___446_4480 = act  in
                               let uu____4481 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4482 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___446_4480.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___446_4480.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___446_4480.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4481;
                                 FStar_Syntax_Syntax.action_typ = uu____4482
                               }  in
                             (uu____4478, uu____4479)
                          in
                       match uu____4450 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4486 =
                               let uu____4487 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4487.FStar_Syntax_Syntax.n  in
                             match uu____4486 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4513 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4513
                                 then
                                   let repr_ts =
                                     let uu____4517 = repr  in
                                     match uu____4517 with
                                     | (us,t,uu____4532) -> (us, t)  in
                                   let repr1 =
                                     let uu____4550 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4550
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4562 =
                                       let uu____4567 =
                                         let uu____4568 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4568 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4567
                                        in
                                     uu____4562 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4586 =
                                       let uu____4589 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4589
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4586
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4592 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4593 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4593 with
                            | (act_typ1,uu____4601,g_t) ->
                                let uu____4603 =
                                  let uu____4610 =
                                    let uu___471_4611 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___471_4611.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___471_4611.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___471_4611.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___471_4611.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___471_4611.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___471_4611.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___471_4611.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___471_4611.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___471_4611.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___471_4611.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___471_4611.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___471_4611.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___471_4611.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___471_4611.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___471_4611.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___471_4611.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___471_4611.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___471_4611.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___471_4611.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___471_4611.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___471_4611.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___471_4611.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___471_4611.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___471_4611.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___471_4611.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___471_4611.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___471_4611.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___471_4611.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___471_4611.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___471_4611.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___471_4611.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___471_4611.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___471_4611.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___471_4611.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___471_4611.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___471_4611.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___471_4611.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___471_4611.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___471_4611.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___471_4611.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___471_4611.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___471_4611.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___471_4611.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___471_4611.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___471_4611.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___471_4611.FStar_TypeChecker_Env.erasable_types_tab);
                                      FStar_TypeChecker_Env.enable_defer_to_tac
                                        =
                                        (uu___471_4611.FStar_TypeChecker_Env.enable_defer_to_tac)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4610
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4603 with
                                 | (act_defn,uu____4614,g_d) ->
                                     ((let uu____4617 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4617
                                       then
                                         let uu____4622 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4624 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4622 uu____4624
                                       else ());
                                      (let uu____4629 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4637 =
                                           let uu____4638 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4638.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4637 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4648) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4671 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4671 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4687 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4687 with
                                                   | (a_tm,uu____4707,g_tm)
                                                       ->
                                                       let uu____4721 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4721 with
                                                        | (repr1,g) ->
                                                            let uu____4734 =
                                                              let uu____4737
                                                                =
                                                                let uu____4740
                                                                  =
                                                                  let uu____4743
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4743
                                                                    (
                                                                    fun _4746
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4746)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4740
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4737
                                                               in
                                                            let uu____4747 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4734,
                                                              uu____4747))))
                                         | uu____4750 ->
                                             let uu____4751 =
                                               let uu____4757 =
                                                 let uu____4759 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4759
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4757)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4751 r
                                          in
                                       match uu____4629 with
                                       | (k,g_k) ->
                                           ((let uu____4776 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4776
                                             then
                                               let uu____4781 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4781
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4789 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4789
                                              then
                                                let uu____4794 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4794
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4807 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4807
                                                   in
                                                let repr_args t =
                                                  let uu____4828 =
                                                    let uu____4829 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4829.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4828 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4881 =
                                                        let uu____4882 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4882.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4881 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4891,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4901 ->
                                                           let uu____4902 =
                                                             let uu____4908 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4908)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4902 r)
                                                  | uu____4917 ->
                                                      let uu____4918 =
                                                        let uu____4924 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4924)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4918 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4934 =
                                                  let uu____4935 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4935.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4934 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4960 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4960 with
                                                     | (bs1,c1) ->
                                                         let uu____4967 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4967
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
                                                              let uu____4978
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4978))
                                                | uu____4981 ->
                                                    let uu____4982 =
                                                      let uu____4988 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4988)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4982 r
                                                 in
                                              (let uu____4992 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4992
                                               then
                                                 let uu____4997 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4997
                                               else ());
                                              (let act2 =
                                                 let uu____5003 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5003 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___544_5017 =
                                                         act1  in
                                                       let uu____5018 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___544_5017.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___544_5017.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___544_5017.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5018
                                                       }
                                                     else
                                                       (let uu____5021 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5028
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5028
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5021
                                                        then
                                                          let uu___549_5033 =
                                                            act1  in
                                                          let uu____5034 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___549_5033.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___549_5033.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___549_5033.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___549_5033.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5034
                                                          }
                                                        else
                                                          (let uu____5037 =
                                                             let uu____5043 =
                                                               let uu____5045
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5047
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____5045
                                                                 uu____5047
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5043)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5037 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5072 =
                      match uu____5072 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5117 =
                        let uu____5118 = tschemes_of repr  in
                        let uu____5123 = tschemes_of return_repr  in
                        let uu____5128 = tschemes_of bind_repr  in
                        let uu____5133 = tschemes_of stronger_repr  in
                        let uu____5138 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5118;
                          FStar_Syntax_Syntax.l_return = uu____5123;
                          FStar_Syntax_Syntax.l_bind = uu____5128;
                          FStar_Syntax_Syntax.l_subcomp = uu____5133;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5138
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5117  in
                    let uu___558_5143 = ed  in
                    let uu____5144 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___558_5143.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___558_5143.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___558_5143.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___558_5143.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5151 = signature  in
                         match uu____5151 with | (us,t,uu____5166) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5144;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___558_5143.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5204 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5204
         then
           let uu____5209 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5209
         else ());
        (let uu____5215 =
           let uu____5220 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5220 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5244 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5244  in
               let uu____5245 =
                 let uu____5252 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5252 bs  in
               (match uu____5245 with
                | (bs1,uu____5258,uu____5259) ->
                    let uu____5260 =
                      let tmp_t =
                        let uu____5270 =
                          let uu____5273 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5278  ->
                                 FStar_Pervasives_Native.Some _5278)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5273
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5270  in
                      let uu____5279 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5279 with
                      | (us,tmp_t1) ->
                          let uu____5296 =
                            let uu____5297 =
                              let uu____5298 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5298
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5297
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5296)
                       in
                    (match uu____5260 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5335 ->
                              let uu____5338 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5345 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5345 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5338
                              then (us, bs2)
                              else
                                (let uu____5356 =
                                   let uu____5362 =
                                     let uu____5364 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5366 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5364 uu____5366
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5362)
                                    in
                                 let uu____5370 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5356
                                   uu____5370))))
            in
         match uu____5215 with
         | (us,bs) ->
             let ed1 =
               let uu___592_5378 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___592_5378.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___592_5378.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___592_5378.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___592_5378.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___592_5378.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___592_5378.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5379 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5379 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5398 =
                    let uu____5403 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5403  in
                  (match uu____5398 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5424 =
                           match uu____5424 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5444 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5444 t  in
                               let uu____5453 =
                                 let uu____5454 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5454 t1  in
                               (us1, uu____5453)
                            in
                         let uu___606_5459 = ed1  in
                         let uu____5460 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5461 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5462 =
                           FStar_List.map
                             (fun a  ->
                                let uu___609_5470 = a  in
                                let uu____5471 =
                                  let uu____5472 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5472  in
                                let uu____5483 =
                                  let uu____5484 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5484  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___609_5470.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___609_5470.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___609_5470.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___609_5470.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5471;
                                  FStar_Syntax_Syntax.action_typ = uu____5483
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___606_5459.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___606_5459.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___606_5459.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___606_5459.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5460;
                           FStar_Syntax_Syntax.combinators = uu____5461;
                           FStar_Syntax_Syntax.actions = uu____5462;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___606_5459.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5496 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5496
                         then
                           let uu____5501 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5501
                         else ());
                        (let env =
                           let uu____5508 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5508
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5543 k =
                           match uu____5543 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5563 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5563 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5572 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5572 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5573 =
                                            let uu____5580 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5580 t1
                                             in
                                          (match uu____5573 with
                                           | (t2,uu____5582,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5585 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5585 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5601 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5603 =
                                                 let uu____5605 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5605
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5601 uu____5603
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5620 ->
                                               let uu____5621 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5628 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5628 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5621
                                               then (g_us, t3)
                                               else
                                                 (let uu____5639 =
                                                    let uu____5645 =
                                                      let uu____5647 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5649 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5647
                                                        uu____5649
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5645)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5639
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5657 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5657
                          then
                            let uu____5662 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5662
                          else ());
                         (let fresh_a_and_wp uu____5678 =
                            let fail1 t =
                              let uu____5691 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5691
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5707 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5707 with
                            | (uu____5718,signature1) ->
                                let uu____5720 =
                                  let uu____5721 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5721.FStar_Syntax_Syntax.n  in
                                (match uu____5720 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5731) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5760)::(wp,uu____5762)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5791 -> fail1 signature1)
                                 | uu____5792 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5806 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5806
                            then
                              let uu____5811 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5811
                            else ()  in
                          let ret_wp =
                            let uu____5817 = fresh_a_and_wp ()  in
                            match uu____5817 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5833 =
                                    let uu____5842 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5849 =
                                      let uu____5858 =
                                        let uu____5865 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5865
                                         in
                                      [uu____5858]  in
                                    uu____5842 :: uu____5849  in
                                  let uu____5884 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5833
                                    uu____5884
                                   in
                                let uu____5887 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5887
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5901 = fresh_a_and_wp ()  in
                             match uu____5901 with
                             | (a,wp_sort_a) ->
                                 let uu____5914 = fresh_a_and_wp ()  in
                                 (match uu____5914 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5930 =
                                          let uu____5939 =
                                            let uu____5946 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5946
                                             in
                                          [uu____5939]  in
                                        let uu____5959 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5930
                                          uu____5959
                                         in
                                      let k =
                                        let uu____5965 =
                                          let uu____5974 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5981 =
                                            let uu____5990 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5997 =
                                              let uu____6006 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6013 =
                                                let uu____6022 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6029 =
                                                  let uu____6038 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6038]  in
                                                uu____6022 :: uu____6029  in
                                              uu____6006 :: uu____6013  in
                                            uu____5990 :: uu____5997  in
                                          uu____5974 :: uu____5981  in
                                        let uu____6081 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5965
                                          uu____6081
                                         in
                                      let uu____6084 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6084
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6098 = fresh_a_and_wp ()  in
                              match uu____6098 with
                              | (a,wp_sort_a) ->
                                  let uu____6111 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6111 with
                                   | (t,uu____6117) ->
                                       let k =
                                         let uu____6121 =
                                           let uu____6130 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6137 =
                                             let uu____6146 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6153 =
                                               let uu____6162 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6162]  in
                                             uu____6146 :: uu____6153  in
                                           uu____6130 :: uu____6137  in
                                         let uu____6193 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6121
                                           uu____6193
                                          in
                                       let uu____6196 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6196
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6210 = fresh_a_and_wp ()  in
                               match uu____6210 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6224 =
                                       let uu____6227 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6227
                                        in
                                     let uu____6228 =
                                       let uu____6229 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6229
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6224
                                       uu____6228
                                      in
                                   let k =
                                     let uu____6241 =
                                       let uu____6250 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6257 =
                                         let uu____6266 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6273 =
                                           let uu____6282 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6289 =
                                             let uu____6298 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6298]  in
                                           uu____6282 :: uu____6289  in
                                         uu____6266 :: uu____6273  in
                                       uu____6250 :: uu____6257  in
                                     let uu____6335 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6241
                                       uu____6335
                                      in
                                   let uu____6338 =
                                     let uu____6343 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6343
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6338
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6375 = fresh_a_and_wp ()  in
                                match uu____6375 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6391 =
                                        let uu____6400 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6407 =
                                          let uu____6416 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6416]  in
                                        uu____6400 :: uu____6407  in
                                      let uu____6441 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6391
                                        uu____6441
                                       in
                                    let uu____6444 =
                                      let uu____6449 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6449
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6444
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6465 = fresh_a_and_wp ()  in
                                 match uu____6465 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6479 =
                                         let uu____6482 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6482
                                          in
                                       let uu____6483 =
                                         let uu____6484 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6484
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6479
                                         uu____6483
                                        in
                                     let wp_sort_b_a =
                                       let uu____6496 =
                                         let uu____6505 =
                                           let uu____6512 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6512
                                            in
                                         [uu____6505]  in
                                       let uu____6525 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6496
                                         uu____6525
                                        in
                                     let k =
                                       let uu____6531 =
                                         let uu____6540 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6547 =
                                           let uu____6556 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6563 =
                                             let uu____6572 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6572]  in
                                           uu____6556 :: uu____6563  in
                                         uu____6540 :: uu____6547  in
                                       let uu____6603 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6531
                                         uu____6603
                                        in
                                     let uu____6606 =
                                       let uu____6611 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6611
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6606
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6627 = fresh_a_and_wp ()  in
                                  match uu____6627 with
                                  | (a,wp_sort_a) ->
                                      let uu____6640 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6640 with
                                       | (t,uu____6646) ->
                                           let k =
                                             let uu____6650 =
                                               let uu____6659 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6666 =
                                                 let uu____6675 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6675]  in
                                               uu____6659 :: uu____6666  in
                                             let uu____6700 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6650 uu____6700
                                              in
                                           let trivial =
                                             let uu____6704 =
                                               let uu____6709 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6709 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6704
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6724 =
                                  let uu____6741 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6741 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6770 ->
                                      let repr =
                                        let uu____6774 = fresh_a_and_wp ()
                                           in
                                        match uu____6774 with
                                        | (a,wp_sort_a) ->
                                            let uu____6787 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6787 with
                                             | (t,uu____6793) ->
                                                 let k =
                                                   let uu____6797 =
                                                     let uu____6806 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6813 =
                                                       let uu____6822 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6822]  in
                                                     uu____6806 :: uu____6813
                                                      in
                                                   let uu____6847 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6797 uu____6847
                                                    in
                                                 let uu____6850 =
                                                   let uu____6855 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6855
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6850
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6899 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6899 with
                                          | (uu____6906,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6909 =
                                                let uu____6916 =
                                                  let uu____6917 =
                                                    let uu____6934 =
                                                      let uu____6945 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6962 =
                                                        let uu____6973 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6973]  in
                                                      uu____6945 ::
                                                        uu____6962
                                                       in
                                                    (repr2, uu____6934)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6917
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6916
                                                 in
                                              uu____6909
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7039 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7039 wp  in
                                        let destruct_repr t =
                                          let uu____7054 =
                                            let uu____7055 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7055.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7054 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7066,(t1,uu____7068)::
                                               (wp,uu____7070)::[])
                                              -> (t1, wp)
                                          | uu____7129 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7145 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7145
                                              FStar_Util.must
                                             in
                                          let uu____7172 = fresh_a_and_wp ()
                                             in
                                          match uu____7172 with
                                          | (a,uu____7180) ->
                                              let x_a =
                                                let uu____7186 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7186
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7194 =
                                                    let uu____7199 =
                                                      let uu____7200 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7200
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7209 =
                                                      let uu____7210 =
                                                        let uu____7219 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7219
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7228 =
                                                        let uu____7239 =
                                                          let uu____7248 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7248
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7239]  in
                                                      uu____7210 ::
                                                        uu____7228
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7199 uu____7209
                                                     in
                                                  uu____7194
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7284 =
                                                  let uu____7293 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7300 =
                                                    let uu____7309 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7309]  in
                                                  uu____7293 :: uu____7300
                                                   in
                                                let uu____7334 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7284 uu____7334
                                                 in
                                              let uu____7337 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7337 with
                                               | (k1,uu____7345,uu____7346)
                                                   ->
                                                   let env1 =
                                                     let uu____7350 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7350
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
                                             let uu____7363 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7363
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7401 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7401
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7402 = fresh_a_and_wp ()
                                              in
                                           match uu____7402 with
                                           | (a,wp_sort_a) ->
                                               let uu____7415 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7415 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7431 =
                                                        let uu____7440 =
                                                          let uu____7447 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7447
                                                           in
                                                        [uu____7440]  in
                                                      let uu____7460 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7431 uu____7460
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
                                                      let uu____7468 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7468
                                                       in
                                                    let wp_g_x =
                                                      let uu____7473 =
                                                        let uu____7478 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7479 =
                                                          let uu____7480 =
                                                            let uu____7489 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7489
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7480]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7478
                                                          uu____7479
                                                         in
                                                      uu____7473
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7520 =
                                                          let uu____7525 =
                                                            let uu____7526 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7526
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7535 =
                                                            let uu____7536 =
                                                              let uu____7539
                                                                =
                                                                let uu____7542
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7543
                                                                  =
                                                                  let uu____7546
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7547
                                                                    =
                                                                    let uu____7550
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7551
                                                                    =
                                                                    let uu____7554
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7554]
                                                                     in
                                                                    uu____7550
                                                                    ::
                                                                    uu____7551
                                                                     in
                                                                  uu____7546
                                                                    ::
                                                                    uu____7547
                                                                   in
                                                                uu____7542 ::
                                                                  uu____7543
                                                                 in
                                                              r :: uu____7539
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7536
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7525
                                                            uu____7535
                                                           in
                                                        uu____7520
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7572 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7572
                                                      then
                                                        let uu____7583 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7590 =
                                                          let uu____7599 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7599]  in
                                                        uu____7583 ::
                                                          uu____7590
                                                      else []  in
                                                    let k =
                                                      let uu____7635 =
                                                        let uu____7644 =
                                                          let uu____7653 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7660 =
                                                            let uu____7669 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7669]  in
                                                          uu____7653 ::
                                                            uu____7660
                                                           in
                                                        let uu____7694 =
                                                          let uu____7703 =
                                                            let uu____7712 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7719 =
                                                              let uu____7728
                                                                =
                                                                let uu____7735
                                                                  =
                                                                  let uu____7736
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7736
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7735
                                                                 in
                                                              let uu____7737
                                                                =
                                                                let uu____7746
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7753
                                                                  =
                                                                  let uu____7762
                                                                    =
                                                                    let uu____7769
                                                                    =
                                                                    let uu____7770
                                                                    =
                                                                    let uu____7779
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7779]
                                                                     in
                                                                    let uu____7798
                                                                    =
                                                                    let uu____7801
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7801
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7770
                                                                    uu____7798
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7769
                                                                     in
                                                                  [uu____7762]
                                                                   in
                                                                uu____7746 ::
                                                                  uu____7753
                                                                 in
                                                              uu____7728 ::
                                                                uu____7737
                                                               in
                                                            uu____7712 ::
                                                              uu____7719
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7703
                                                           in
                                                        FStar_List.append
                                                          uu____7644
                                                          uu____7694
                                                         in
                                                      let uu____7846 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7635 uu____7846
                                                       in
                                                    let uu____7849 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7849 with
                                                     | (k1,uu____7857,uu____7858)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___804_7868
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___804_7868.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun _7870  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7870)
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
                                              (let uu____7897 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7911 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7911 with
                                                    | (usubst,uvs) ->
                                                        let uu____7934 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7935 =
                                                          let uu___817_7936 =
                                                            act  in
                                                          let uu____7937 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7938 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___817_7936.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___817_7936.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___817_7936.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7937;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7938
                                                          }  in
                                                        (uu____7934,
                                                          uu____7935))
                                                  in
                                               match uu____7897 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7942 =
                                                       let uu____7943 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7943.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7942 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7969 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7969
                                                         then
                                                           let uu____7972 =
                                                             let uu____7975 =
                                                               let uu____7976
                                                                 =
                                                                 let uu____7977
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7977
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7976
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7975
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7972
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8000 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8001 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8001 with
                                                    | (act_typ1,uu____8009,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___834_8012 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___834_8012.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          }  in
                                                        ((let uu____8015 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8015
                                                          then
                                                            let uu____8019 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8021 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8023 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8019
                                                              uu____8021
                                                              uu____8023
                                                          else ());
                                                         (let uu____8028 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8028
                                                          with
                                                          | (act_defn,uu____8036,g_a)
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
                                                              let uu____8040
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
                                                                    let uu____8076
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8076
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8088)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8095
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8095
                                                                     in
                                                                    let uu____8098
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8098
                                                                    with
                                                                    | 
                                                                    (k1,uu____8112,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8116
                                                                    ->
                                                                    let uu____8117
                                                                    =
                                                                    let uu____8123
                                                                    =
                                                                    let uu____8125
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8127
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8125
                                                                    uu____8127
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8123)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8117
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8040
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
                                                                    let uu____8145
                                                                    =
                                                                    let uu____8146
                                                                    =
                                                                    let uu____8147
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8147
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8146
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8145);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8149
                                                                    =
                                                                    let uu____8150
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8150.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8149
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8175
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8175
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8182
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8182
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8202
                                                                    =
                                                                    let uu____8203
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8203]
                                                                     in
                                                                    let uu____8204
                                                                    =
                                                                    let uu____8215
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8215]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8202;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8204;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8240
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8240))
                                                                    | 
                                                                    uu____8243
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8245
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8267
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8267))
                                                                     in
                                                                    match uu____8245
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
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
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___884_8286
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___884_8286.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___884_8286.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___884_8286.FStar_Syntax_Syntax.action_params);
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
                                match uu____6724 with
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
                                      let uu____8329 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8329 ts1
                                       in
                                    let combinators =
                                      {
                                        FStar_Syntax_Syntax.ret_wp = ret_wp;
                                        FStar_Syntax_Syntax.bind_wp = bind_wp;
                                        FStar_Syntax_Syntax.stronger =
                                          stronger;
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else1;
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
                                          uu____8341 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8342 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8343 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___904_8346 = ed2  in
                                      let uu____8347 = cl signature  in
                                      let uu____8348 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___907_8356 = a  in
                                             let uu____8357 =
                                               let uu____8358 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8358
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8383 =
                                               let uu____8384 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8384
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___907_8356.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___907_8356.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___907_8356.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___907_8356.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8357;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8383
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___904_8346.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___904_8346.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___904_8346.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___904_8346.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8347;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8348;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___904_8346.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8410 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8410
                                      then
                                        let uu____8415 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8415
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
        let uu____8441 =
          let uu____8456 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8456 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8441 env ed quals
  
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
        let fail1 uu____8506 =
          let uu____8507 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8513 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8507 uu____8513  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8557)::(wp,uu____8559)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8588 -> fail1 ())
        | uu____8589 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8602 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8602
       then
         let uu____8607 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8607
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8624 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8624.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____8636 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8640 =
                let uu____8641 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8641 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8640
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8650 =
                   let uu____8651 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8651 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8650
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8659 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8659))
           in
        if uu____8636
        then
          let uu____8662 =
            let uu____8668 =
              let uu____8670 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8673 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8670 uu____8673
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8668)  in
          FStar_Errors.raise_error uu____8662 r
        else ());
       (let uu____8680 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8680 with
        | (us,lift,lift_ty) ->
            ((let uu____8694 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8694
              then
                let uu____8699 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8705 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8699 uu____8705
              else ());
             (let uu____8714 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8714 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____8732 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.source
                         in
                      let uu____8734 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.target
                         in
                      let uu____8736 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____8732 uu____8734 s uu____8736
                       in
                    let uu____8739 =
                      let uu____8746 =
                        let uu____8751 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____8751
                          (fun uu____8768  ->
                             match uu____8768 with
                             | (t,u) ->
                                 let uu____8779 =
                                   let uu____8780 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____8780
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____8779, u))
                         in
                      match uu____8746 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____8799 =
                              let uu____8800 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____8800.FStar_Syntax_Syntax.n  in
                            match uu____8799 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____8812)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____8840 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____8840 with
                                 | (a',uu____8850)::bs1 ->
                                     let uu____8870 =
                                       let uu____8871 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____8871
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____8937 =
                                       let uu____8950 =
                                         let uu____8953 =
                                           let uu____8954 =
                                             let uu____8961 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____8961)  in
                                           FStar_Syntax_Syntax.NT uu____8954
                                            in
                                         [uu____8953]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____8950
                                        in
                                     FStar_All.pipe_right uu____8870
                                       uu____8937)
                            | uu____8976 ->
                                let uu____8977 =
                                  let uu____8983 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____8983)
                                   in
                                FStar_Errors.raise_error uu____8977 r
                             in
                          let uu____8995 =
                            let uu____9006 =
                              let uu____9011 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9018 =
                                let uu____9019 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9019
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9011 r sub1.FStar_Syntax_Syntax.source
                                u_a uu____9018
                               in
                            match uu____9006 with
                            | (f_sort,g) ->
                                let uu____9040 =
                                  let uu____9047 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9047
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9040, g)
                             in
                          (match uu____8995 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9114 =
                                 let uu____9119 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9120 =
                                   let uu____9121 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9121
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9119 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____9120
                                  in
                               (match uu____9114 with
                                | (repr,g_repr) ->
                                    let uu____9138 =
                                      let uu____9143 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9144 =
                                        let uu____9146 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9148 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9146 uu____9148
                                         in
                                      pure_wp_uvar uu____9143 repr uu____9144
                                        r
                                       in
                                    (match uu____9138 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9160 =
                                             let uu____9161 =
                                               let uu____9162 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9162]  in
                                             let uu____9163 =
                                               let uu____9174 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9174]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9161;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9163;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9160
                                            in
                                         let uu____9207 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9210 =
                                           let uu____9211 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9211 guard_wp
                                            in
                                         (uu____9207, uu____9210))))
                       in
                    match uu____8739 with
                    | (k,g_k) ->
                        ((let uu____9221 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9221
                          then
                            let uu____9226 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9226
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9235 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9235
                           then
                             let uu____9240 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9240
                           else ());
                          (let sub2 =
                             let uu___1000_9246 = sub1  in
                             let uu____9247 =
                               let uu____9250 =
                                 let uu____9251 =
                                   let uu____9254 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9254
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9251)  in
                               FStar_Pervasives_Native.Some uu____9250  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1000_9246.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1000_9246.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9247;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9266 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9266
                            then
                              let uu____9271 =
                                FStar_Syntax_Print.sub_eff_to_string sub2  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9271
                            else ());
                           sub2)))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let check_and_gen1 env1 t k =
          let uu____9308 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9308  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9311 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9311
        then tc_layered_lift env sub1
        else
          (let uu____9318 =
             let uu____9325 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9325
              in
           match uu____9318 with
           | (a,wp_a_src) ->
               let uu____9332 =
                 let uu____9339 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9339
                  in
               (match uu____9332 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9347 =
                        let uu____9350 =
                          let uu____9351 =
                            let uu____9358 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9358)  in
                          FStar_Syntax_Syntax.NT uu____9351  in
                        [uu____9350]  in
                      FStar_Syntax_Subst.subst uu____9347 wp_b_tgt  in
                    let expected_k =
                      let uu____9366 =
                        let uu____9375 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9382 =
                          let uu____9391 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9391]  in
                        uu____9375 :: uu____9382  in
                      let uu____9416 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9366 uu____9416  in
                    let repr_type eff_name a1 wp =
                      (let uu____9438 =
                         let uu____9440 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9440  in
                       if uu____9438
                       then
                         let uu____9443 =
                           let uu____9449 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9449)
                            in
                         let uu____9453 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9443 uu____9453
                       else ());
                      (let uu____9456 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9456 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9489 =
                               let uu____9490 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9490
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9489
                              in
                           let uu____9497 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9498 =
                             let uu____9505 =
                               let uu____9506 =
                                 let uu____9523 =
                                   let uu____9534 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9543 =
                                     let uu____9554 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9554]  in
                                   uu____9534 :: uu____9543  in
                                 (repr, uu____9523)  in
                               FStar_Syntax_Syntax.Tm_app uu____9506  in
                             FStar_Syntax_Syntax.mk uu____9505  in
                           uu____9498 FStar_Pervasives_Native.None uu____9497)
                       in
                    let uu____9599 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9772 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9783 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9783 with
                              | (usubst,uvs1) ->
                                  let uu____9806 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9807 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9806, uu____9807)
                            else (env, lift_wp)  in
                          (match uu____9772 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9857 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9857))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9928 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9943 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9943 with
                              | (usubst,uvs) ->
                                  let uu____9968 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9968)
                            else ([], lift)  in
                          (match uu____9928 with
                           | (uvs,lift1) ->
                               ((let uu____10004 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10004
                                 then
                                   let uu____10008 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10008
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10014 =
                                   let uu____10021 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10021 lift1
                                    in
                                 match uu____10014 with
                                 | (lift2,comp,uu____10046) ->
                                     let uu____10047 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10047 with
                                      | (uu____10076,lift_wp,lift_elab) ->
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
                                            let uu____10108 =
                                              let uu____10119 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10119
                                               in
                                            let uu____10136 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10108, uu____10136)
                                          else
                                            (let uu____10165 =
                                               let uu____10176 =
                                                 let uu____10185 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10185)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10176
                                                in
                                             let uu____10200 =
                                               let uu____10209 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10209)  in
                                             (uu____10165, uu____10200))))))
                       in
                    (match uu____9599 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1084_10273 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1084_10273.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1084_10273.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1084_10273.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1084_10273.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1084_10273.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1084_10273.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1084_10273.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1084_10273.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1084_10273.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1084_10273.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1084_10273.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1084_10273.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1084_10273.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1084_10273.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1084_10273.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1084_10273.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1084_10273.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1084_10273.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1084_10273.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1084_10273.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1084_10273.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1084_10273.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1084_10273.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1084_10273.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1084_10273.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1084_10273.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1084_10273.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1084_10273.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1084_10273.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1084_10273.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1084_10273.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1084_10273.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1084_10273.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1084_10273.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1084_10273.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1084_10273.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1084_10273.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1084_10273.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1084_10273.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1084_10273.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1084_10273.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1084_10273.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1084_10273.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1084_10273.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1084_10273.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1084_10273.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1084_10273.FStar_TypeChecker_Env.enable_defer_to_tac)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10306 =
                                 let uu____10311 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10311 with
                                 | (usubst,uvs1) ->
                                     let uu____10334 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10335 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10334, uu____10335)
                                  in
                               (match uu____10306 with
                                | (env2,lift2) ->
                                    let uu____10340 =
                                      let uu____10347 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10347
                                       in
                                    (match uu____10340 with
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
                                             sub1.FStar_Syntax_Syntax.source
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
                                             let uu____10373 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10374 =
                                               let uu____10381 =
                                                 let uu____10382 =
                                                   let uu____10399 =
                                                     let uu____10410 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10419 =
                                                       let uu____10430 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10430]  in
                                                     uu____10410 ::
                                                       uu____10419
                                                      in
                                                   (lift_wp1, uu____10399)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10382
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10381
                                                in
                                             uu____10374
                                               FStar_Pervasives_Native.None
                                               uu____10373
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10478 =
                                             let uu____10487 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10494 =
                                               let uu____10503 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10510 =
                                                 let uu____10519 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10519]  in
                                               uu____10503 :: uu____10510  in
                                             uu____10487 :: uu____10494  in
                                           let uu____10550 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10478 uu____10550
                                            in
                                         let uu____10553 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10553 with
                                          | (expected_k2,uu____10563,uu____10564)
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
                                                   let uu____10572 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10572))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10580 =
                             let uu____10582 =
                               let uu____10584 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10584
                                 FStar_List.length
                                in
                             uu____10582 <> Prims.int_one  in
                           if uu____10580
                           then
                             let uu____10607 =
                               let uu____10613 =
                                 let uu____10615 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10617 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10619 =
                                   let uu____10621 =
                                     let uu____10623 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10623
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10621
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10615 uu____10617 uu____10619
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10613)
                                in
                             FStar_Errors.raise_error uu____10607 r
                           else ());
                          (let uu____10650 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10653 =
                                  let uu____10655 =
                                    let uu____10658 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10658
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10655
                                    FStar_List.length
                                   in
                                uu____10653 <> Prims.int_one)
                              in
                           if uu____10650
                           then
                             let uu____10697 =
                               let uu____10703 =
                                 let uu____10705 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10707 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10709 =
                                   let uu____10711 =
                                     let uu____10713 =
                                       let uu____10716 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10716
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10713
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10711
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10705 uu____10707 uu____10709
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10703)
                                in
                             FStar_Errors.raise_error uu____10697 r
                           else ());
                          (let uu___1121_10758 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1121_10758.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1121_10758.FStar_Syntax_Syntax.target);
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
    fun uu____10789  ->
      fun r  ->
        match uu____10789 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10812 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10840 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10840 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10871 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10871 c  in
                     let uu____10880 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10880, uvs1, tps1, c1))
               in
            (match uu____10812 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10900 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10900 with
                  | (tps2,c2) ->
                      let uu____10915 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10915 with
                       | (tps3,env3,us) ->
                           let uu____10933 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10933 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10959)::uu____10960 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10979 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10987 =
                                    let uu____10989 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10989  in
                                  if uu____10987
                                  then
                                    let uu____10992 =
                                      let uu____10998 =
                                        let uu____11000 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11002 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11000 uu____11002
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10998)
                                       in
                                    FStar_Errors.raise_error uu____10992 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11010 =
                                    let uu____11011 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11011
                                     in
                                  match uu____11010 with
                                  | (uvs2,t) ->
                                      let uu____11040 =
                                        let uu____11045 =
                                          let uu____11058 =
                                            let uu____11059 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11059.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11058)  in
                                        match uu____11045 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11074,c5)) -> ([], c5)
                                        | (uu____11116,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11155 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11040 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11187 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11187 with
                                               | (uu____11192,t1) ->
                                                   let uu____11194 =
                                                     let uu____11200 =
                                                       let uu____11202 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11204 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11208 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11202
                                                         uu____11204
                                                         uu____11208
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11200)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11194 r)
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
      fun n1  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11250 = FStar_Ident.string_of_lid m  in
              let uu____11252 = FStar_Ident.string_of_lid n1  in
              let uu____11254 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11250 uu____11252
                uu____11254
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11262 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11262 with
            | (us,t,ty) ->
                let uu____11278 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11278 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11291 =
                         let uu____11296 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11296
                           (fun uu____11313  ->
                              match uu____11313 with
                              | (t1,u) ->
                                  let uu____11324 =
                                    let uu____11325 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11325
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11324, u))
                          in
                       match uu____11291 with
                       | (a,u_a) ->
                           let uu____11333 =
                             let uu____11338 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11338
                               (fun uu____11355  ->
                                  match uu____11355 with
                                  | (t1,u) ->
                                      let uu____11366 =
                                        let uu____11367 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11367
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11366, u))
                              in
                           (match uu____11333 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11384 =
                                    let uu____11385 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11385.FStar_Syntax_Syntax.n  in
                                  match uu____11384 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11397) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11425 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11425 with
                                       | (a',uu____11435)::(b',uu____11437)::bs1
                                           ->
                                           let uu____11467 =
                                             let uu____11468 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11468
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11534 =
                                             let uu____11547 =
                                               let uu____11550 =
                                                 let uu____11551 =
                                                   let uu____11558 =
                                                     let uu____11561 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11561
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11558)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11551
                                                  in
                                               let uu____11574 =
                                                 let uu____11577 =
                                                   let uu____11578 =
                                                     let uu____11585 =
                                                       let uu____11588 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11588
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11585)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11578
                                                    in
                                                 [uu____11577]  in
                                               uu____11550 :: uu____11574  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11547
                                              in
                                           FStar_All.pipe_right uu____11467
                                             uu____11534)
                                  | uu____11609 ->
                                      let uu____11610 =
                                        let uu____11616 =
                                          let uu____11618 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11620 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11618 uu____11620
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11616)
                                         in
                                      FStar_Errors.raise_error uu____11610 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11653 =
                                  let uu____11664 =
                                    let uu____11669 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11670 =
                                      let uu____11671 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11671
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11669 r m u_a uu____11670
                                     in
                                  match uu____11664 with
                                  | (repr,g) ->
                                      let uu____11692 =
                                        let uu____11699 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11699
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11692, g)
                                   in
                                (match uu____11653 with
                                 | (f,guard_f) ->
                                     let uu____11731 =
                                       let x_a =
                                         let uu____11749 =
                                           let uu____11750 =
                                             let uu____11751 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11751
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11750
                                            in
                                         FStar_All.pipe_right uu____11749
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11767 =
                                         let uu____11772 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____11791 =
                                           let uu____11792 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____11792
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11772 r n1 u_b uu____11791
                                          in
                                       match uu____11767 with
                                       | (repr,g) ->
                                           let uu____11813 =
                                             let uu____11820 =
                                               let uu____11821 =
                                                 let uu____11822 =
                                                   let uu____11825 =
                                                     let uu____11828 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11828
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11825
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11822
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11821
                                                in
                                             FStar_All.pipe_right uu____11820
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____11813, g)
                                        in
                                     (match uu____11731 with
                                      | (g,guard_g) ->
                                          let uu____11872 =
                                            let uu____11877 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____11878 =
                                              let uu____11879 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11879
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11877 r p u_b uu____11878
                                             in
                                          (match uu____11872 with
                                           | (repr,guard_repr) ->
                                               let uu____11894 =
                                                 let uu____11899 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____11900 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____11899
                                                   repr uu____11900 r
                                                  in
                                               (match uu____11894 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____11912 =
                                                        let uu____11915 =
                                                          let uu____11916 =
                                                            let uu____11917 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____11917]  in
                                                          let uu____11918 =
                                                            let uu____11929 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____11929]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____11916;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____11918;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____11915
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____11912
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
                                                     (let uu____11989 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____11989
                                                      then
                                                        let uu____11993 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____11999 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____11993
                                                          uu____11999
                                                      else ());
                                                     (let uu____12009 =
                                                        let uu____12015 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12015)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12009);
                                                     (let uu____12019 =
                                                        let uu____12020 =
                                                          let uu____12023 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12023
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12020)
                                                         in
                                                      ((us1, t), uu____12019)))))))))))
  