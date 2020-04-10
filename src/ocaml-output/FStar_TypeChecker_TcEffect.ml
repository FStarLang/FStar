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
                let not_an_arrow_error comb n t r =
                  let uu____1234 =
                    let uu____1240 =
                      let uu____1242 = FStar_Util.string_of_int n  in
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
                   let uu____1642 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1642 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1666 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1666 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1687 = fresh_a_and_u_a "a"  in
                              match uu____1687 with
                              | (a,u_a) ->
                                  let uu____1707 = fresh_a_and_u_a "b"  in
                                  (match uu____1707 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1736 =
                                           let uu____1737 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1737.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1736 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1749) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1777 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1777 with
                                              | (a',uu____1787)::(b',uu____1789)::bs1
                                                  ->
                                                  let uu____1819 =
                                                    let uu____1820 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1820
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1886 =
                                                    let uu____1899 =
                                                      let uu____1902 =
                                                        let uu____1903 =
                                                          let uu____1910 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1910)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1903
                                                         in
                                                      let uu____1917 =
                                                        let uu____1920 =
                                                          let uu____1921 =
                                                            let uu____1928 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1928)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1921
                                                           in
                                                        [uu____1920]  in
                                                      uu____1902 ::
                                                        uu____1917
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1899
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1819 uu____1886)
                                         | uu____1943 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1967 =
                                         let uu____1978 =
                                           let uu____1983 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1984 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1983 u_a
                                             uu____1984
                                            in
                                         match uu____1978 with
                                         | (repr1,g) ->
                                             let uu____1999 =
                                               let uu____2006 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2006
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____1999, g)
                                          in
                                       (match uu____1967 with
                                        | (f,guard_f) ->
                                            let uu____2046 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2059 =
                                                let uu____2064 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2083 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2064 u_b
                                                  uu____2083
                                                 in
                                              match uu____2059 with
                                              | (repr1,g) ->
                                                  let uu____2098 =
                                                    let uu____2105 =
                                                      let uu____2106 =
                                                        let uu____2107 =
                                                          let uu____2110 =
                                                            let uu____2113 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2113
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2110
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2107
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2106
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2105
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2098, g)
                                               in
                                            (match uu____2046 with
                                             | (g,guard_g) ->
                                                 let uu____2165 =
                                                   let uu____2170 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2171 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2170
                                                     u_b uu____2171
                                                    in
                                                 (match uu____2165 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2188 =
                                                        let uu____2193 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2194 =
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                           in
                                                        pure_wp_uvar
                                                          uu____2193 repr1
                                                          uu____2194 r
                                                         in
                                                      (match uu____2188 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2214 =
                                                               let uu____2217
                                                                 =
                                                                 let uu____2218
                                                                   =
                                                                   let uu____2219
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2219]
                                                                    in
                                                                 let uu____2220
                                                                   =
                                                                   let uu____2231
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2231]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2218;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2220;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2217
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2214
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
                                                            (let uu____2290 =
                                                               let uu____2293
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2293
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2290)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2322 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2322 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2350 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2350 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2375 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2375
                          then
                            let uu____2380 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2386 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2380 uu____2386
                          else ());
                         (let uu____2395 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2395 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2416 = fresh_a_and_u_a "a"  in
                                match uu____2416 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2445 =
                                        let uu____2446 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2446.FStar_Syntax_Syntax.n  in
                                      match uu____2445 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2458) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2486 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2486 with
                                           | (a',uu____2496)::bs1 ->
                                               let uu____2516 =
                                                 let uu____2517 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2517
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2615 =
                                                 let uu____2628 =
                                                   let uu____2631 =
                                                     let uu____2632 =
                                                       let uu____2639 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2639)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2632
                                                      in
                                                   [uu____2631]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2628
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2516 uu____2615)
                                      | uu____2654 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2672 =
                                      let uu____2683 =
                                        let uu____2688 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2689 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2688 u uu____2689
                                         in
                                      match uu____2683 with
                                      | (repr1,g) ->
                                          let uu____2704 =
                                            let uu____2711 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2711
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2704, g)
                                       in
                                    (match uu____2672 with
                                     | (f,guard_f) ->
                                         let uu____2751 =
                                           let uu____2756 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2757 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2756 u
                                             uu____2757
                                            in
                                         (match uu____2751 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2774 =
                                                let uu____2779 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2780 =
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   in
                                                pure_wp_uvar uu____2779 ret_t
                                                  uu____2780 r
                                                 in
                                              (match uu____2774 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2798 =
                                                       let uu____2799 =
                                                         let uu____2800 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2800]  in
                                                       let uu____2801 =
                                                         let uu____2812 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2812]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2799;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2801;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2798
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2867 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2867
                                                     then
                                                       let uu____2872 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2872
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
                                                     (let uu____2879 =
                                                        let uu____2882 =
                                                          let uu____2883 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2883
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2882
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2879)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else =
                     let if_then_else_ts =
                       let uu____2914 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2914 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2954 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2954 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2978 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2978 with
                          | (us,t) ->
                              let uu____2997 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2997 with
                               | (uu____3014,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____3018 = fresh_a_and_u_a "a"  in
                                     match uu____3018 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3047 =
                                             let uu____3048 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3048.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3047 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3060) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3088 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3088 with
                                                | (a',uu____3098)::bs1 ->
                                                    let uu____3118 =
                                                      let uu____3119 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3119
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3217 =
                                                      let uu____3230 =
                                                        let uu____3233 =
                                                          let uu____3234 =
                                                            let uu____3241 =
                                                              let uu____3244
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3244
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3241)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3234
                                                           in
                                                        [uu____3233]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3230
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3118 uu____3217)
                                           | uu____3265 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3283 =
                                           let uu____3294 =
                                             let uu____3299 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3300 =
                                               let uu____3301 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3301
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3299 u_a
                                               uu____3300
                                              in
                                           match uu____3294 with
                                           | (repr1,g) ->
                                               let uu____3322 =
                                                 let uu____3329 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3329
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3322, g)
                                            in
                                         (match uu____3283 with
                                          | (f_bs,guard_f) ->
                                              let uu____3369 =
                                                let uu____3380 =
                                                  let uu____3385 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3386 =
                                                    let uu____3387 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3387
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3385 u_a
                                                    uu____3386
                                                   in
                                                match uu____3380 with
                                                | (repr1,g) ->
                                                    let uu____3408 =
                                                      let uu____3415 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3415
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3408, g)
                                                 in
                                              (match uu____3369 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3462 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3462
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3470 =
                                                     let uu____3475 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3494 =
                                                       let uu____3495 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3495
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3475
                                                       u_a uu____3494
                                                      in
                                                   (match uu____3470 with
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
                                                         (let uu____3555 =
                                                            let uu____3558 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3558
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3555,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else;
                   (let r =
                      let uu____3571 =
                        let uu____3574 =
                          let uu____3583 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3583 FStar_Util.must  in
                        FStar_All.pipe_right uu____3574
                          FStar_Pervasives_Native.snd
                         in
                      uu____3571.FStar_Syntax_Syntax.pos  in
                    let uu____3644 = if_then_else  in
                    match uu____3644 with
                    | (ite_us,ite_t,uu____3659) ->
                        let uu____3672 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3672 with
                         | (us,ite_t1) ->
                             let uu____3679 =
                               let uu____3694 =
                                 let uu____3695 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3695.FStar_Syntax_Syntax.n  in
                               match uu____3694 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3713,uu____3714) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3740 =
                                     let uu____3753 =
                                       let uu____3758 =
                                         let uu____3761 =
                                           let uu____3770 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3770
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3761
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3758
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3753
                                       (fun l  ->
                                          let uu____3926 = l  in
                                          match uu____3926 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3740 with
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
                                            let uu____4003 =
                                              let uu____4004 =
                                                let uu____4007 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____4007
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____4004
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____4003
                                             in
                                          uu____3998
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3995, uu____3997, f, g, p))
                               | uu____4038 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3679 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____4067 =
                                    let uu____4076 = stronger_repr  in
                                    match uu____4076 with
                                    | (uu____4097,subcomp_t,subcomp_ty) ->
                                        let uu____4112 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____4112 with
                                         | (uu____4125,subcomp_t1) ->
                                             let uu____4127 =
                                               let uu____4138 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____4138 with
                                               | (uu____4153,subcomp_ty1) ->
                                                   let uu____4155 =
                                                     let uu____4156 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____4156.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____4155 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4170) ->
                                                        let uu____4191 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        (match uu____4191
                                                         with
                                                         | (bs_except_last,last_b)
                                                             ->
                                                             let uu____4297 =
                                                               FStar_All.pipe_right
                                                                 bs_except_last
                                                                 (FStar_List.map
                                                                    FStar_Pervasives_Native.snd)
                                                                in
                                                             let uu____4324 =
                                                               let uu____4327
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   last_b
                                                                   FStar_List.hd
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____4327
                                                                 FStar_Pervasives_Native.snd
                                                                in
                                                             (uu____4297,
                                                               uu____4324))
                                                    | uu____4370 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             (match uu____4127 with
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
                                                  let uu____4483 = aux f_t
                                                     in
                                                  let uu____4486 = aux g_t
                                                     in
                                                  (uu____4483, uu____4486)))
                                     in
                                  (match uu____4067 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4503 =
                                         let aux t =
                                           let uu____4520 =
                                             let uu____4527 =
                                               let uu____4528 =
                                                 let uu____4555 =
                                                   let uu____4572 =
                                                     let uu____4581 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4581
                                                      in
                                                   (uu____4572,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4555,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4528
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4527
                                              in
                                           uu____4520
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4622 = aux subcomp_f  in
                                         let uu____4623 = aux subcomp_g  in
                                         (uu____4622, uu____4623)  in
                                       (match uu____4503 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4627 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4627
                                              then
                                                let uu____4632 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4634 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4632 uu____4634
                                              else ());
                                             (let uu____4639 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4639 with
                                              | (uu____4646,uu____4647,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4650 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4650 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4652 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4652 with
                                                    | (uu____4659,uu____4660,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4666 =
                                                              let uu____4671
                                                                =
                                                                let uu____4672
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4672
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4673
                                                                =
                                                                let uu____4674
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4674]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4671
                                                                uu____4673
                                                               in
                                                            uu____4666
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4707 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4707 g_g
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
                        (let uu____4731 =
                           let uu____4737 =
                             let uu____4739 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4739
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4737)
                            in
                         FStar_Errors.raise_error uu____4731 r)
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
                                     let uu____4858 =
                                       let uu____4863 =
                                         let uu____4864 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4864 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4863
                                        in
                                     uu____4858 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4882 =
                                       let uu____4885 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4885
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4882
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4888 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4889 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4889 with
                            | (act_typ1,uu____4897,g_t) ->
                                let uu____4899 =
                                  let uu____4906 =
                                    let uu___477_4907 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___477_4907.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___477_4907.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___477_4907.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___477_4907.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___477_4907.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___477_4907.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___477_4907.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___477_4907.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___477_4907.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___477_4907.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___477_4907.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___477_4907.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___477_4907.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___477_4907.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___477_4907.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___477_4907.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___477_4907.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___477_4907.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___477_4907.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___477_4907.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___477_4907.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___477_4907.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___477_4907.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___477_4907.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___477_4907.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___477_4907.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___477_4907.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___477_4907.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___477_4907.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___477_4907.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___477_4907.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___477_4907.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___477_4907.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___477_4907.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___477_4907.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___477_4907.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___477_4907.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___477_4907.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___477_4907.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___477_4907.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___477_4907.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___477_4907.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___477_4907.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___477_4907.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___477_4907.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___477_4907.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4906
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4899 with
                                 | (act_defn,uu____4910,g_d) ->
                                     ((let uu____4913 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4913
                                       then
                                         let uu____4918 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4920 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4918 uu____4920
                                       else ());
                                      (let uu____4925 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4933 =
                                           let uu____4934 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4934.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4933 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4944) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4967 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4967 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4983 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4983 with
                                                   | (a_tm,uu____5003,g_tm)
                                                       ->
                                                       let uu____5017 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____5017 with
                                                        | (repr1,g) ->
                                                            let uu____5030 =
                                                              let uu____5033
                                                                =
                                                                let uu____5036
                                                                  =
                                                                  let uu____5039
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____5039
                                                                    (
                                                                    fun
                                                                    uu____5042
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____5042)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____5036
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5033
                                                               in
                                                            let uu____5043 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____5030,
                                                              uu____5043))))
                                         | uu____5046 ->
                                             let uu____5047 =
                                               let uu____5053 =
                                                 let uu____5055 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____5055
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____5053)
                                                in
                                             FStar_Errors.raise_error
                                               uu____5047 r
                                          in
                                       match uu____4925 with
                                       | (k,g_k) ->
                                           ((let uu____5072 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____5072
                                             then
                                               let uu____5077 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____5077
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____5085 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____5085
                                              then
                                                let uu____5090 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____5090
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____5103 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____5103
                                                   in
                                                let repr_args t =
                                                  let uu____5124 =
                                                    let uu____5125 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____5125.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____5124 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head,a::is) ->
                                                      let uu____5177 =
                                                        let uu____5178 =
                                                          FStar_Syntax_Subst.compress
                                                            head
                                                           in
                                                        uu____5178.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____5177 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____5187,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____5197 ->
                                                           let uu____5198 =
                                                             let uu____5204 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____5204)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5198 r)
                                                  | uu____5213 ->
                                                      let uu____5214 =
                                                        let uu____5220 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5220)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____5214 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____5230 =
                                                  let uu____5231 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____5231.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____5230 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____5256 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____5256 with
                                                     | (bs1,c1) ->
                                                         let uu____5263 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____5263
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
                                                              let uu____5274
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____5274))
                                                | uu____5277 ->
                                                    let uu____5278 =
                                                      let uu____5284 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____5284)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____5278 r
                                                 in
                                              (let uu____5288 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____5288
                                               then
                                                 let uu____5293 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5293
                                               else ());
                                              (let act2 =
                                                 let uu____5299 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5299 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___550_5313 =
                                                         act1  in
                                                       let uu____5314 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___550_5313.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___550_5313.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___550_5313.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5314
                                                       }
                                                     else
                                                       (let uu____5317 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5324
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5324
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5317
                                                        then
                                                          let uu___555_5329 =
                                                            act1  in
                                                          let uu____5330 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___555_5329.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___555_5329.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___555_5329.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___555_5329.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5330
                                                          }
                                                        else
                                                          (let uu____5333 =
                                                             let uu____5339 =
                                                               let uu____5341
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5343
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____5341
                                                                 uu____5343
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5339)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5333 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5368 =
                      match uu____5368 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5413 =
                        let uu____5414 = tschemes_of repr  in
                        let uu____5419 = tschemes_of return_repr  in
                        let uu____5424 = tschemes_of bind_repr  in
                        let uu____5429 = tschemes_of stronger_repr  in
                        let uu____5434 = tschemes_of if_then_else  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5414;
                          FStar_Syntax_Syntax.l_return = uu____5419;
                          FStar_Syntax_Syntax.l_bind = uu____5424;
                          FStar_Syntax_Syntax.l_subcomp = uu____5429;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5434
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5413  in
                    let uu___564_5439 = ed  in
                    let uu____5440 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___564_5439.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___564_5439.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___564_5439.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___564_5439.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5447 = signature  in
                         match uu____5447 with | (us,t,uu____5462) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5440;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___564_5439.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5500 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5500
         then
           let uu____5505 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5505
         else ());
        (let uu____5511 =
           let uu____5516 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5516 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5540 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5540  in
               let uu____5541 =
                 let uu____5548 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5548 bs  in
               (match uu____5541 with
                | (bs1,uu____5554,uu____5555) ->
                    let uu____5556 =
                      let tmp_t =
                        let uu____5566 =
                          let uu____5569 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5574  ->
                                 FStar_Pervasives_Native.Some uu____5574)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5569
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5566  in
                      let uu____5575 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5575 with
                      | (us,tmp_t1) ->
                          let uu____5592 =
                            let uu____5593 =
                              let uu____5594 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5594
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5593
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5592)
                       in
                    (match uu____5556 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5631 ->
                              let uu____5634 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5641 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5641 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5634
                              then (us, bs2)
                              else
                                (let uu____5652 =
                                   let uu____5658 =
                                     let uu____5660 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5662 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5660 uu____5662
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5658)
                                    in
                                 let uu____5666 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5652
                                   uu____5666))))
            in
         match uu____5511 with
         | (us,bs) ->
             let ed1 =
               let uu___598_5674 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___598_5674.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___598_5674.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___598_5674.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___598_5674.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___598_5674.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___598_5674.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5675 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5675 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5694 =
                    let uu____5699 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5699  in
                  (match uu____5694 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5720 =
                           match uu____5720 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5740 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5740 t  in
                               let uu____5749 =
                                 let uu____5750 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5750 t1  in
                               (us1, uu____5749)
                            in
                         let uu___612_5755 = ed1  in
                         let uu____5756 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5757 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5758 =
                           FStar_List.map
                             (fun a  ->
                                let uu___615_5766 = a  in
                                let uu____5767 =
                                  let uu____5768 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5768  in
                                let uu____5779 =
                                  let uu____5780 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5780  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___615_5766.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___615_5766.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___615_5766.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___615_5766.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5767;
                                  FStar_Syntax_Syntax.action_typ = uu____5779
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___612_5755.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___612_5755.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___612_5755.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___612_5755.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5756;
                           FStar_Syntax_Syntax.combinators = uu____5757;
                           FStar_Syntax_Syntax.actions = uu____5758;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___612_5755.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5792 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5792
                         then
                           let uu____5797 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5797
                         else ());
                        (let env =
                           let uu____5804 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5804
                             ed_bs
                            in
                         let check_and_gen' comb n env_opt uu____5839 k =
                           match uu____5839 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5859 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5859 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5868 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5868 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5869 =
                                            let uu____5876 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5876 t1
                                             in
                                          (match uu____5869 with
                                           | (t2,uu____5878,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5881 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5881 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5897 =
                                                 FStar_Util.string_of_int n
                                                  in
                                               let uu____5899 =
                                                 let uu____5901 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5901
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5897 uu____5899
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5916 ->
                                               let uu____5917 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5924 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5924 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5917
                                               then (g_us, t3)
                                               else
                                                 (let uu____5935 =
                                                    let uu____5941 =
                                                      let uu____5943 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5945 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5943
                                                        uu____5945
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5941)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5935
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5953 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5953
                          then
                            let uu____5958 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5958
                          else ());
                         (let fresh_a_and_wp uu____5974 =
                            let fail t =
                              let uu____5987 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5987
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____6003 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____6003 with
                            | (uu____6014,signature1) ->
                                let uu____6016 =
                                  let uu____6017 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____6017.FStar_Syntax_Syntax.n  in
                                (match uu____6016 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____6027) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____6056)::(wp,uu____6058)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6087 -> fail signature1)
                                 | uu____6088 -> fail signature1)
                             in
                          let log_combinator s ts =
                            let uu____6102 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____6102
                            then
                              let uu____6107 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____6107
                            else ()  in
                          let ret_wp =
                            let uu____6113 = fresh_a_and_wp ()  in
                            match uu____6113 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____6129 =
                                    let uu____6138 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____6145 =
                                      let uu____6154 =
                                        let uu____6161 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6161
                                         in
                                      [uu____6154]  in
                                    uu____6138 :: uu____6145  in
                                  let uu____6180 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____6129
                                    uu____6180
                                   in
                                let uu____6183 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6183
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6197 = fresh_a_and_wp ()  in
                             match uu____6197 with
                             | (a,wp_sort_a) ->
                                 let uu____6210 = fresh_a_and_wp ()  in
                                 (match uu____6210 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6226 =
                                          let uu____6235 =
                                            let uu____6242 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6242
                                             in
                                          [uu____6235]  in
                                        let uu____6255 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6226
                                          uu____6255
                                         in
                                      let k =
                                        let uu____6261 =
                                          let uu____6270 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____6277 =
                                            let uu____6286 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6293 =
                                              let uu____6302 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6309 =
                                                let uu____6318 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6325 =
                                                  let uu____6334 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6334]  in
                                                uu____6318 :: uu____6325  in
                                              uu____6302 :: uu____6309  in
                                            uu____6286 :: uu____6293  in
                                          uu____6270 :: uu____6277  in
                                        let uu____6377 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____6261
                                          uu____6377
                                         in
                                      let uu____6380 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6380
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6394 = fresh_a_and_wp ()  in
                              match uu____6394 with
                              | (a,wp_sort_a) ->
                                  let uu____6407 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6407 with
                                   | (t,uu____6413) ->
                                       let k =
                                         let uu____6417 =
                                           let uu____6426 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6433 =
                                             let uu____6442 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6449 =
                                               let uu____6458 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6458]  in
                                             uu____6442 :: uu____6449  in
                                           uu____6426 :: uu____6433  in
                                         let uu____6489 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6417
                                           uu____6489
                                          in
                                       let uu____6492 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6492
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6506 = fresh_a_and_wp ()  in
                               match uu____6506 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6520 =
                                       let uu____6523 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6523
                                        in
                                     let uu____6524 =
                                       let uu____6525 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6525
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6520
                                       uu____6524
                                      in
                                   let k =
                                     let uu____6537 =
                                       let uu____6546 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6553 =
                                         let uu____6562 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6569 =
                                           let uu____6578 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6585 =
                                             let uu____6594 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6594]  in
                                           uu____6578 :: uu____6585  in
                                         uu____6562 :: uu____6569  in
                                       uu____6546 :: uu____6553  in
                                     let uu____6631 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6537
                                       uu____6631
                                      in
                                   let uu____6634 =
                                     let uu____6639 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6639
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6634
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6671 = fresh_a_and_wp ()  in
                                match uu____6671 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6687 =
                                        let uu____6696 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6703 =
                                          let uu____6712 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6712]  in
                                        uu____6696 :: uu____6703  in
                                      let uu____6737 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6687
                                        uu____6737
                                       in
                                    let uu____6740 =
                                      let uu____6745 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6745
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6740
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6761 = fresh_a_and_wp ()  in
                                 match uu____6761 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6775 =
                                         let uu____6778 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6778
                                          in
                                       let uu____6779 =
                                         let uu____6780 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6780
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6775
                                         uu____6779
                                        in
                                     let wp_sort_b_a =
                                       let uu____6792 =
                                         let uu____6801 =
                                           let uu____6808 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6808
                                            in
                                         [uu____6801]  in
                                       let uu____6821 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6792
                                         uu____6821
                                        in
                                     let k =
                                       let uu____6827 =
                                         let uu____6836 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6843 =
                                           let uu____6852 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6859 =
                                             let uu____6868 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6868]  in
                                           uu____6852 :: uu____6859  in
                                         uu____6836 :: uu____6843  in
                                       let uu____6899 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6827
                                         uu____6899
                                        in
                                     let uu____6902 =
                                       let uu____6907 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6907
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6902
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6923 = fresh_a_and_wp ()  in
                                  match uu____6923 with
                                  | (a,wp_sort_a) ->
                                      let uu____6936 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6936 with
                                       | (t,uu____6942) ->
                                           let k =
                                             let uu____6946 =
                                               let uu____6955 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6962 =
                                                 let uu____6971 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6971]  in
                                               uu____6955 :: uu____6962  in
                                             let uu____6996 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6946 uu____6996
                                              in
                                           let trivial =
                                             let uu____7000 =
                                               let uu____7005 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____7005 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____7000
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____7020 =
                                  let uu____7037 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____7037 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____7066 ->
                                      let repr =
                                        let uu____7070 = fresh_a_and_wp ()
                                           in
                                        match uu____7070 with
                                        | (a,wp_sort_a) ->
                                            let uu____7083 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____7083 with
                                             | (t,uu____7089) ->
                                                 let k =
                                                   let uu____7093 =
                                                     let uu____7102 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____7109 =
                                                       let uu____7118 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____7118]  in
                                                     uu____7102 :: uu____7109
                                                      in
                                                   let uu____7143 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7093 uu____7143
                                                    in
                                                 let uu____7146 =
                                                   let uu____7151 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____7151
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7146
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7195 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____7195 with
                                          | (uu____7202,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____7205 =
                                                let uu____7212 =
                                                  let uu____7213 =
                                                    let uu____7230 =
                                                      let uu____7241 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7258 =
                                                        let uu____7269 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7269]  in
                                                      uu____7241 ::
                                                        uu____7258
                                                       in
                                                    (repr2, uu____7230)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____7213
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____7212
                                                 in
                                              uu____7205
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7335 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7335 wp  in
                                        let destruct_repr t =
                                          let uu____7350 =
                                            let uu____7351 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7351.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7350 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7362,(t1,uu____7364)::
                                               (wp,uu____7366)::[])
                                              -> (t1, wp)
                                          | uu____7425 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7441 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7441
                                              FStar_Util.must
                                             in
                                          let uu____7468 = fresh_a_and_wp ()
                                             in
                                          match uu____7468 with
                                          | (a,uu____7476) ->
                                              let x_a =
                                                let uu____7482 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7482
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7490 =
                                                    let uu____7495 =
                                                      let uu____7496 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7496
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7505 =
                                                      let uu____7506 =
                                                        let uu____7515 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7515
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7524 =
                                                        let uu____7535 =
                                                          let uu____7544 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7544
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7535]  in
                                                      uu____7506 ::
                                                        uu____7524
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7495 uu____7505
                                                     in
                                                  uu____7490
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7580 =
                                                  let uu____7589 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7596 =
                                                    let uu____7605 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7605]  in
                                                  uu____7589 :: uu____7596
                                                   in
                                                let uu____7630 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7580 uu____7630
                                                 in
                                              let uu____7633 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7633 with
                                               | (k1,uu____7641,uu____7642)
                                                   ->
                                                   let env1 =
                                                     let uu____7646 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7646
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
                                             let uu____7659 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7659
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7697 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7697
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7698 = fresh_a_and_wp ()
                                              in
                                           match uu____7698 with
                                           | (a,wp_sort_a) ->
                                               let uu____7711 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7711 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7727 =
                                                        let uu____7736 =
                                                          let uu____7743 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7743
                                                           in
                                                        [uu____7736]  in
                                                      let uu____7756 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7727 uu____7756
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
                                                      let uu____7764 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7764
                                                       in
                                                    let wp_g_x =
                                                      let uu____7769 =
                                                        let uu____7774 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7775 =
                                                          let uu____7776 =
                                                            let uu____7785 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7785
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7776]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7774
                                                          uu____7775
                                                         in
                                                      uu____7769
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7816 =
                                                          let uu____7821 =
                                                            let uu____7822 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7822
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7831 =
                                                            let uu____7832 =
                                                              let uu____7835
                                                                =
                                                                let uu____7838
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7839
                                                                  =
                                                                  let uu____7842
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7843
                                                                    =
                                                                    let uu____7846
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7847
                                                                    =
                                                                    let uu____7850
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7850]
                                                                     in
                                                                    uu____7846
                                                                    ::
                                                                    uu____7847
                                                                     in
                                                                  uu____7842
                                                                    ::
                                                                    uu____7843
                                                                   in
                                                                uu____7838 ::
                                                                  uu____7839
                                                                 in
                                                              r :: uu____7835
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7832
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7821
                                                            uu____7831
                                                           in
                                                        uu____7816
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7868 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7868
                                                      then
                                                        let uu____7879 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7886 =
                                                          let uu____7895 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7895]  in
                                                        uu____7879 ::
                                                          uu____7886
                                                      else []  in
                                                    let k =
                                                      let uu____7931 =
                                                        let uu____7940 =
                                                          let uu____7949 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7956 =
                                                            let uu____7965 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7965]  in
                                                          uu____7949 ::
                                                            uu____7956
                                                           in
                                                        let uu____7990 =
                                                          let uu____7999 =
                                                            let uu____8008 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____8015 =
                                                              let uu____8024
                                                                =
                                                                let uu____8031
                                                                  =
                                                                  let uu____8032
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____8032
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____8031
                                                                 in
                                                              let uu____8033
                                                                =
                                                                let uu____8042
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____8049
                                                                  =
                                                                  let uu____8058
                                                                    =
                                                                    let uu____8065
                                                                    =
                                                                    let uu____8066
                                                                    =
                                                                    let uu____8075
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____8075]
                                                                     in
                                                                    let uu____8094
                                                                    =
                                                                    let uu____8097
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____8097
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____8066
                                                                    uu____8094
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____8065
                                                                     in
                                                                  [uu____8058]
                                                                   in
                                                                uu____8042 ::
                                                                  uu____8049
                                                                 in
                                                              uu____8024 ::
                                                                uu____8033
                                                               in
                                                            uu____8008 ::
                                                              uu____8015
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7999
                                                           in
                                                        FStar_List.append
                                                          uu____7940
                                                          uu____7990
                                                         in
                                                      let uu____8142 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7931 uu____8142
                                                       in
                                                    let uu____8145 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____8145 with
                                                     | (k1,uu____8153,uu____8154)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___810_8164
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___810_8164.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun uu____8166 
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8166)
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
                                              (let uu____8193 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8207 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____8207 with
                                                    | (usubst,uvs) ->
                                                        let uu____8230 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____8231 =
                                                          let uu___823_8232 =
                                                            act  in
                                                          let uu____8233 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____8234 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___823_8232.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___823_8232.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___823_8232.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8233;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8234
                                                          }  in
                                                        (uu____8230,
                                                          uu____8231))
                                                  in
                                               match uu____8193 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____8238 =
                                                       let uu____8239 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____8239.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____8238 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____8265 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____8265
                                                         then
                                                           let uu____8268 =
                                                             let uu____8271 =
                                                               let uu____8272
                                                                 =
                                                                 let uu____8273
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8273
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8272
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8271
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8268
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8296 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8297 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8297 with
                                                    | (act_typ1,uu____8305,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___840_8308 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___840_8308.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____8311 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8311
                                                          then
                                                            let uu____8315 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8317 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8319 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8315
                                                              uu____8317
                                                              uu____8319
                                                          else ());
                                                         (let uu____8324 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8324
                                                          with
                                                          | (act_defn,uu____8332,g_a)
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
                                                              let uu____8336
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
                                                                    let uu____8372
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8372
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8384)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8391
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8391
                                                                     in
                                                                    let uu____8394
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8394
                                                                    with
                                                                    | 
                                                                    (k1,uu____8408,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8412
                                                                    ->
                                                                    let uu____8413
                                                                    =
                                                                    let uu____8419
                                                                    =
                                                                    let uu____8421
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8423
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8421
                                                                    uu____8423
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8419)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8413
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8336
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
                                                                    let uu____8441
                                                                    =
                                                                    let uu____8442
                                                                    =
                                                                    let uu____8443
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8443
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8442
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8441);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8445
                                                                    =
                                                                    let uu____8446
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8446.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8445
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8471
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8471
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8478
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8478
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8498
                                                                    =
                                                                    let uu____8499
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8499]
                                                                     in
                                                                    let uu____8500
                                                                    =
                                                                    let uu____8511
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8511]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8498;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8500;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8536
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8536))
                                                                    | 
                                                                    uu____8539
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8541
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8563
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8563))
                                                                     in
                                                                    match uu____8541
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
                                                                    let uu___890_8582
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___890_8582.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___890_8582.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___890_8582.FStar_Syntax_Syntax.action_params);
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
                                match uu____7020 with
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
                                      let uu____8625 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8625 ts1
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
                                          uu____8637 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8638 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8639 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___910_8642 = ed2  in
                                      let uu____8643 = cl signature  in
                                      let uu____8644 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___913_8652 = a  in
                                             let uu____8653 =
                                               let uu____8654 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8654
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8679 =
                                               let uu____8680 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8680
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___913_8652.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___913_8652.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___913_8652.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___913_8652.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8653;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8679
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___910_8642.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___910_8642.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___910_8642.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___910_8642.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8643;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8644;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___910_8642.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8706 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8706
                                      then
                                        let uu____8711 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8711
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
        let uu____8737 =
          let uu____8752 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8752 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8737 env ed quals
  
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
        let fail uu____8802 =
          let uu____8803 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8809 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8803 uu____8809  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8853)::(wp,uu____8855)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8884 -> fail ())
        | uu____8885 -> fail ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub  ->
      (let uu____8898 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8898
       then
         let uu____8903 = FStar_Syntax_Print.sub_eff_to_string sub  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8903
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8920 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8920.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub.FStar_Syntax_Syntax.target
           in
        let uu____8932 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8936 =
                let uu____8937 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8937 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8936
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8946 =
                   let uu____8947 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8947 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8946
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8955 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8955))
           in
        if uu____8932
        then
          let uu____8958 =
            let uu____8964 =
              let uu____8966 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8969 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8966 uu____8969
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8964)  in
          FStar_Errors.raise_error uu____8958 r
        else ());
       (let uu____8976 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8976 with
        | (us,lift,lift_ty) ->
            ((let uu____8990 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8990
              then
                let uu____8995 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____9001 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8995 uu____9001
              else ());
             (let uu____9010 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____9010 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____9028 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.source
                         in
                      let uu____9030 =
                        FStar_Ident.string_of_lid
                          sub.FStar_Syntax_Syntax.target
                         in
                      let uu____9032 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____9028 uu____9030 s uu____9032
                       in
                    let uu____9035 =
                      let uu____9042 =
                        let uu____9047 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____9047
                          (fun uu____9064  ->
                             match uu____9064 with
                             | (t,u) ->
                                 let uu____9075 =
                                   let uu____9076 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____9076
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____9075, u))
                         in
                      match uu____9042 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____9095 =
                              let uu____9096 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____9096.FStar_Syntax_Syntax.n  in
                            match uu____9095 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____9108)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____9136 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____9136 with
                                 | (a',uu____9146)::bs1 ->
                                     let uu____9166 =
                                       let uu____9167 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____9167
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____9233 =
                                       let uu____9246 =
                                         let uu____9249 =
                                           let uu____9250 =
                                             let uu____9257 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____9257)  in
                                           FStar_Syntax_Syntax.NT uu____9250
                                            in
                                         [uu____9249]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____9246
                                        in
                                     FStar_All.pipe_right uu____9166
                                       uu____9233)
                            | uu____9272 ->
                                let uu____9273 =
                                  let uu____9279 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____9279)
                                   in
                                FStar_Errors.raise_error uu____9273 r
                             in
                          let uu____9291 =
                            let uu____9302 =
                              let uu____9307 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9314 =
                                let uu____9315 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9315
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9307 r sub.FStar_Syntax_Syntax.source
                                u_a uu____9314
                               in
                            match uu____9302 with
                            | (f_sort,g) ->
                                let uu____9336 =
                                  let uu____9343 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9343
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9336, g)
                             in
                          (match uu____9291 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9410 =
                                 let uu____9415 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9416 =
                                   let uu____9417 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9417
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9415 r
                                   sub.FStar_Syntax_Syntax.target u_a
                                   uu____9416
                                  in
                               (match uu____9410 with
                                | (repr,g_repr) ->
                                    let uu____9434 =
                                      let uu____9439 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9440 =
                                        let uu____9442 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9444 =
                                          FStar_Ident.string_of_lid
                                            sub.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9442 uu____9444
                                         in
                                      pure_wp_uvar uu____9439 repr uu____9440
                                        r
                                       in
                                    (match uu____9434 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9456 =
                                             let uu____9457 =
                                               let uu____9458 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9458]  in
                                             let uu____9459 =
                                               let uu____9470 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9470]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9457;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9459;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9456
                                            in
                                         let uu____9503 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9506 =
                                           let uu____9507 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9507 guard_wp
                                            in
                                         (uu____9503, uu____9506))))
                       in
                    match uu____9035 with
                    | (k,g_k) ->
                        ((let uu____9517 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9517
                          then
                            let uu____9522 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9522
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9531 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9531
                           then
                             let uu____9536 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9536
                           else ());
                          (let sub1 =
                             let uu___1006_9542 = sub  in
                             let uu____9543 =
                               let uu____9546 =
                                 let uu____9547 =
                                   let uu____9550 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9550
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9547)  in
                               FStar_Pervasives_Native.Some uu____9546  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1006_9542.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1006_9542.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9543;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9562 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9562
                            then
                              let uu____9567 =
                                FStar_Syntax_Print.sub_eff_to_string sub1  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9567
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
          let uu____9604 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9604  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target
           in
        let uu____9607 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9607
        then tc_layered_lift env sub
        else
          (let uu____9614 =
             let uu____9621 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source
                in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9621
              in
           match uu____9614 with
           | (a,wp_a_src) ->
               let uu____9628 =
                 let uu____9635 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9635
                  in
               (match uu____9628 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9643 =
                        let uu____9646 =
                          let uu____9647 =
                            let uu____9654 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9654)  in
                          FStar_Syntax_Syntax.NT uu____9647  in
                        [uu____9646]  in
                      FStar_Syntax_Subst.subst uu____9643 wp_b_tgt  in
                    let expected_k =
                      let uu____9662 =
                        let uu____9671 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9678 =
                          let uu____9687 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9687]  in
                        uu____9671 :: uu____9678  in
                      let uu____9712 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9662 uu____9712  in
                    let repr_type eff_name a1 wp =
                      (let uu____9734 =
                         let uu____9736 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9736  in
                       if uu____9734
                       then
                         let uu____9739 =
                           let uu____9745 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9745)
                            in
                         let uu____9749 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9739 uu____9749
                       else ());
                      (let uu____9752 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9752 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9785 =
                               let uu____9786 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9786
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9785
                              in
                           let uu____9793 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9794 =
                             let uu____9801 =
                               let uu____9802 =
                                 let uu____9819 =
                                   let uu____9830 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9839 =
                                     let uu____9850 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9850]  in
                                   uu____9830 :: uu____9839  in
                                 (repr, uu____9819)  in
                               FStar_Syntax_Syntax.Tm_app uu____9802  in
                             FStar_Syntax_Syntax.mk uu____9801  in
                           uu____9794 FStar_Pervasives_Native.None uu____9793)
                       in
                    let uu____9895 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____10068 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____10079 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____10079 with
                              | (usubst,uvs1) ->
                                  let uu____10102 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____10103 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____10102, uu____10103)
                            else (env, lift_wp)  in
                          (match uu____10068 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____10153 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____10153))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____10224 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10239 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____10239 with
                              | (usubst,uvs) ->
                                  let uu____10264 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____10264)
                            else ([], lift)  in
                          (match uu____10224 with
                           | (uvs,lift1) ->
                               ((let uu____10300 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10300
                                 then
                                   let uu____10304 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10304
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10310 =
                                   let uu____10317 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10317 lift1
                                    in
                                 match uu____10310 with
                                 | (lift2,comp,uu____10342) ->
                                     let uu____10343 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10343 with
                                      | (uu____10372,lift_wp,lift_elab) ->
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
                                            let uu____10404 =
                                              let uu____10415 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10415
                                               in
                                            let uu____10432 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10404, uu____10432)
                                          else
                                            (let uu____10461 =
                                               let uu____10472 =
                                                 let uu____10481 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10481)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10472
                                                in
                                             let uu____10496 =
                                               let uu____10505 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10505)  in
                                             (uu____10461, uu____10496))))))
                       in
                    (match uu____9895 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1090_10569 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1090_10569.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1090_10569.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1090_10569.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1090_10569.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1090_10569.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1090_10569.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1090_10569.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1090_10569.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1090_10569.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1090_10569.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1090_10569.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1090_10569.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1090_10569.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1090_10569.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1090_10569.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1090_10569.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1090_10569.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1090_10569.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1090_10569.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1090_10569.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1090_10569.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1090_10569.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1090_10569.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1090_10569.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1090_10569.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1090_10569.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1090_10569.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1090_10569.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1090_10569.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1090_10569.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1090_10569.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1090_10569.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1090_10569.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1090_10569.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1090_10569.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1090_10569.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1090_10569.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1090_10569.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1090_10569.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1090_10569.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1090_10569.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1090_10569.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1090_10569.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1090_10569.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1090_10569.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1090_10569.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10602 =
                                 let uu____10607 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10607 with
                                 | (usubst,uvs1) ->
                                     let uu____10630 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10631 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10630, uu____10631)
                                  in
                               (match uu____10602 with
                                | (env2,lift2) ->
                                    let uu____10636 =
                                      let uu____10643 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10643
                                       in
                                    (match uu____10636 with
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
                                             let uu____10669 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10670 =
                                               let uu____10677 =
                                                 let uu____10678 =
                                                   let uu____10695 =
                                                     let uu____10706 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10715 =
                                                       let uu____10726 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10726]  in
                                                     uu____10706 ::
                                                       uu____10715
                                                      in
                                                   (lift_wp1, uu____10695)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10678
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10677
                                                in
                                             uu____10670
                                               FStar_Pervasives_Native.None
                                               uu____10669
                                              in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10774 =
                                             let uu____10783 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10790 =
                                               let uu____10799 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10806 =
                                                 let uu____10815 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10815]  in
                                               uu____10799 :: uu____10806  in
                                             uu____10783 :: uu____10790  in
                                           let uu____10846 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10774 uu____10846
                                            in
                                         let uu____10849 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10849 with
                                          | (expected_k2,uu____10859,uu____10860)
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
                                                   let uu____10868 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10868))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10876 =
                             let uu____10878 =
                               let uu____10880 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10880
                                 FStar_List.length
                                in
                             uu____10878 <> Prims.int_one  in
                           if uu____10876
                           then
                             let uu____10903 =
                               let uu____10909 =
                                 let uu____10911 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10913 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10915 =
                                   let uu____10917 =
                                     let uu____10919 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10919
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10917
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10911 uu____10913 uu____10915
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10909)
                                in
                             FStar_Errors.raise_error uu____10903 r
                           else ());
                          (let uu____10946 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10949 =
                                  let uu____10951 =
                                    let uu____10954 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10954
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10951
                                    FStar_List.length
                                   in
                                uu____10949 <> Prims.int_one)
                              in
                           if uu____10946
                           then
                             let uu____10993 =
                               let uu____10999 =
                                 let uu____11001 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source
                                    in
                                 let uu____11003 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target
                                    in
                                 let uu____11005 =
                                   let uu____11007 =
                                     let uu____11009 =
                                       let uu____11012 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____11012
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____11009
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____11007
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____11001 uu____11003 uu____11005
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10999)
                                in
                             FStar_Errors.raise_error uu____10993 r
                           else ());
                          (let uu___1127_11054 = sub  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1127_11054.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1127_11054.FStar_Syntax_Syntax.target);
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
    fun uu____11085  ->
      fun r  ->
        match uu____11085 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____11108 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11136 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____11136 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____11167 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____11167 c  in
                     let uu____11176 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____11176, uvs1, tps1, c1))
               in
            (match uu____11108 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____11196 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____11196 with
                  | (tps2,c2) ->
                      let uu____11211 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____11211 with
                       | (tps3,env3,us) ->
                           let uu____11229 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____11229 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____11255)::uu____11256 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11275 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____11283 =
                                    let uu____11285 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____11285  in
                                  if uu____11283
                                  then
                                    let uu____11288 =
                                      let uu____11294 =
                                        let uu____11296 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11298 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11296 uu____11298
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11294)
                                       in
                                    FStar_Errors.raise_error uu____11288 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11306 =
                                    let uu____11307 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11307
                                     in
                                  match uu____11306 with
                                  | (uvs2,t) ->
                                      let uu____11336 =
                                        let uu____11341 =
                                          let uu____11354 =
                                            let uu____11355 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11355.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11354)  in
                                        match uu____11341 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11370,c5)) -> ([], c5)
                                        | (uu____11412,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11451 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11336 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11483 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11483 with
                                               | (uu____11488,t1) ->
                                                   let uu____11490 =
                                                     let uu____11496 =
                                                       let uu____11498 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11500 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11504 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11498
                                                         uu____11500
                                                         uu____11504
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11496)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11490 r)
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
              let uu____11546 = FStar_Ident.string_of_lid m  in
              let uu____11548 = FStar_Ident.string_of_lid n  in
              let uu____11550 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11546 uu____11548
                uu____11550
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            let uu____11558 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts
               in
            match uu____11558 with
            | (us,t,ty) ->
                let uu____11574 = FStar_Syntax_Subst.open_univ_vars us ty  in
                (match uu____11574 with
                 | (us1,ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                        in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11587 =
                         let uu____11592 = FStar_Syntax_Util.type_u ()  in
                         FStar_All.pipe_right uu____11592
                           (fun uu____11609  ->
                              match uu____11609 with
                              | (t1,u) ->
                                  let uu____11620 =
                                    let uu____11621 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1
                                       in
                                    FStar_All.pipe_right uu____11621
                                      FStar_Syntax_Syntax.mk_binder
                                     in
                                  (uu____11620, u))
                          in
                       match uu____11587 with
                       | (a,u_a) ->
                           let uu____11629 =
                             let uu____11634 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11634
                               (fun uu____11651  ->
                                  match uu____11651 with
                                  | (t1,u) ->
                                      let uu____11662 =
                                        let uu____11663 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11663
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11662, u))
                              in
                           (match uu____11629 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11680 =
                                    let uu____11681 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11681.FStar_Syntax_Syntax.n  in
                                  match uu____11680 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11693) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11721 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11721 with
                                       | (a',uu____11731)::(b',uu____11733)::bs1
                                           ->
                                           let uu____11763 =
                                             let uu____11764 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11764
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11830 =
                                             let uu____11843 =
                                               let uu____11846 =
                                                 let uu____11847 =
                                                   let uu____11854 =
                                                     let uu____11857 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11857
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11854)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11847
                                                  in
                                               let uu____11870 =
                                                 let uu____11873 =
                                                   let uu____11874 =
                                                     let uu____11881 =
                                                       let uu____11884 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11884
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11881)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11874
                                                    in
                                                 [uu____11873]  in
                                               uu____11846 :: uu____11870  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11843
                                              in
                                           FStar_All.pipe_right uu____11763
                                             uu____11830)
                                  | uu____11905 ->
                                      let uu____11906 =
                                        let uu____11912 =
                                          let uu____11914 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11916 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11914 uu____11916
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11912)
                                         in
                                      FStar_Errors.raise_error uu____11906 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11949 =
                                  let uu____11960 =
                                    let uu____11965 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11966 =
                                      let uu____11967 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11967
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11965 r m u_a uu____11966
                                     in
                                  match uu____11960 with
                                  | (repr,g) ->
                                      let uu____11988 =
                                        let uu____11995 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11995
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11988, g)
                                   in
                                (match uu____11949 with
                                 | (f,guard_f) ->
                                     let uu____12027 =
                                       let x_a =
                                         let uu____12045 =
                                           let uu____12046 =
                                             let uu____12047 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____12047
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____12046
                                            in
                                         FStar_All.pipe_right uu____12045
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____12063 =
                                         let uu____12068 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____12087 =
                                           let uu____12088 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____12088
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____12068 r n u_b uu____12087
                                          in
                                       match uu____12063 with
                                       | (repr,g) ->
                                           let uu____12109 =
                                             let uu____12116 =
                                               let uu____12117 =
                                                 let uu____12118 =
                                                   let uu____12121 =
                                                     let uu____12124 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12124
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12121
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12118
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12117
                                                in
                                             FStar_All.pipe_right uu____12116
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____12109, g)
                                        in
                                     (match uu____12027 with
                                      | (g,guard_g) ->
                                          let uu____12168 =
                                            let uu____12173 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____12174 =
                                              let uu____12175 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____12175
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12173 r p u_b uu____12174
                                             in
                                          (match uu____12168 with
                                           | (repr,guard_repr) ->
                                               let uu____12190 =
                                                 let uu____12195 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs
                                                    in
                                                 let uu____12196 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name
                                                    in
                                                 pure_wp_uvar uu____12195
                                                   repr uu____12196 r
                                                  in
                                               (match uu____12190 with
                                                | (pure_wp_uvar1,g_pure_wp_uvar)
                                                    ->
                                                    let k =
                                                      let uu____12208 =
                                                        let uu____12211 =
                                                          let uu____12212 =
                                                            let uu____12213 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            [uu____12213]  in
                                                          let uu____12214 =
                                                            let uu____12225 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg
                                                               in
                                                            [uu____12225]  in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12212;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12214;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          }  in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12211
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12208
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
                                                     (let uu____12285 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme
                                                         in
                                                      if uu____12285
                                                      then
                                                        let uu____12289 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t)
                                                           in
                                                        let uu____12295 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k)
                                                           in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12289
                                                          uu____12295
                                                      else ());
                                                     (let uu____12305 =
                                                        let uu____12311 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name
                                                           in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12311)
                                                         in
                                                      FStar_Errors.log_issue
                                                        r uu____12305);
                                                     (let uu____12315 =
                                                        let uu____12316 =
                                                          let uu____12319 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____12319
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1)
                                                           in
                                                        (us1, uu____12316)
                                                         in
                                                      ((us1, t), uu____12315)))))))))))
  