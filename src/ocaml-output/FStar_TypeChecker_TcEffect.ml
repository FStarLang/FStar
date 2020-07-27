open Prims
let (dmff_cps_and_elaborate :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Syntax_Syntax.sigelt Prims.list * FStar_Syntax_Syntax.eff_decl *
        FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option))
  = fun env -> fun ed -> FStar_TypeChecker_DMFF.cps_and_elaborate env ed
let (check_and_gen :
  FStar_TypeChecker_Env.env ->
    Prims.string ->
      Prims.string ->
        Prims.int ->
          (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) ->
            (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term *
              FStar_Syntax_Syntax.typ))
  =
  fun env ->
    fun eff_name ->
      fun comb ->
        fun n ->
          fun uu____54 ->
            match uu____54 with
            | (us, t) ->
                let uu____73 = FStar_Syntax_Subst.open_univ_vars us t in
                (match uu____73 with
                 | (us1, t1) ->
                     let uu____86 =
                       let uu____91 =
                         let uu____98 =
                           FStar_TypeChecker_Env.push_univ_vars env us1 in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____98 t1 in
                       match uu____91 with
                       | (t2, lc, g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ))) in
                     (match uu____86 with
                      | (t2, ty) ->
                          let uu____115 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2 in
                          (match uu____115 with
                           | (g_us, t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty in
                               (if (FStar_List.length g_us) <> n
                                then
                                  (let error =
                                     let uu____135 =
                                       FStar_Util.string_of_int n in
                                     let uu____136 =
                                       let uu____137 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length in
                                       FStar_All.pipe_right uu____137
                                         FStar_Util.string_of_int in
                                     let uu____140 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3) in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____135 uu____136
                                       uu____140 in
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                       error) t3.FStar_Syntax_Syntax.pos;
                                   (match us1 with
                                    | [] -> ()
                                    | uu____146 ->
                                        let uu____147 =
                                          ((FStar_List.length us1) =
                                             (FStar_List.length g_us))
                                            &&
                                            (FStar_List.forall2
                                               (fun u1 ->
                                                  fun u2 ->
                                                    let uu____153 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2 in
                                                    uu____153 =
                                                      Prims.int_zero) us1
                                               g_us) in
                                        if uu____147
                                        then ()
                                        else
                                          (let uu____155 =
                                             let uu____160 =
                                               let uu____161 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1 in
                                               let uu____162 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____161
                                                 uu____162 in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____160) in
                                           FStar_Errors.raise_error uu____155
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
  fun env ->
    fun t ->
      fun reason ->
        fun r ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____194 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid in
              FStar_All.pipe_right uu____194 FStar_Util.must in
            let uu____199 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts in
            match uu____199 with
            | (uu____204, pure_wp_t) ->
                let uu____206 =
                  let uu____207 =
                    FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                  [uu____207] in
                FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____206 r in
          let uu____240 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t in
          match uu____240 with
          | (pure_wp_uvar, uu____258, guard_wp) -> (pure_wp_uvar, guard_wp)
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env ->
    fun t ->
      fun k ->
        (let uu____292 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffectsTc") in
         if uu____292
         then
           let uu____293 = FStar_Syntax_Print.term_to_string t in
           let uu____294 =
             match k with
             | FStar_Pervasives_Native.None -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1 in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____293 uu____294
         else ());
        (let env1 =
           let uu___54_298 = env in
           {
             FStar_TypeChecker_Env.solver =
               (uu___54_298.FStar_TypeChecker_Env.solver);
             FStar_TypeChecker_Env.range =
               (uu___54_298.FStar_TypeChecker_Env.range);
             FStar_TypeChecker_Env.curmodule =
               (uu___54_298.FStar_TypeChecker_Env.curmodule);
             FStar_TypeChecker_Env.gamma =
               (uu___54_298.FStar_TypeChecker_Env.gamma);
             FStar_TypeChecker_Env.gamma_sig =
               (uu___54_298.FStar_TypeChecker_Env.gamma_sig);
             FStar_TypeChecker_Env.gamma_cache =
               (uu___54_298.FStar_TypeChecker_Env.gamma_cache);
             FStar_TypeChecker_Env.modules =
               (uu___54_298.FStar_TypeChecker_Env.modules);
             FStar_TypeChecker_Env.expected_typ =
               (uu___54_298.FStar_TypeChecker_Env.expected_typ);
             FStar_TypeChecker_Env.sigtab =
               (uu___54_298.FStar_TypeChecker_Env.sigtab);
             FStar_TypeChecker_Env.attrtab =
               (uu___54_298.FStar_TypeChecker_Env.attrtab);
             FStar_TypeChecker_Env.instantiate_imp =
               (uu___54_298.FStar_TypeChecker_Env.instantiate_imp);
             FStar_TypeChecker_Env.effects =
               (uu___54_298.FStar_TypeChecker_Env.effects);
             FStar_TypeChecker_Env.generalize =
               (uu___54_298.FStar_TypeChecker_Env.generalize);
             FStar_TypeChecker_Env.letrecs =
               (uu___54_298.FStar_TypeChecker_Env.letrecs);
             FStar_TypeChecker_Env.top_level =
               (uu___54_298.FStar_TypeChecker_Env.top_level);
             FStar_TypeChecker_Env.check_uvars =
               (uu___54_298.FStar_TypeChecker_Env.check_uvars);
             FStar_TypeChecker_Env.use_eq =
               (uu___54_298.FStar_TypeChecker_Env.use_eq);
             FStar_TypeChecker_Env.use_eq_strict = true;
             FStar_TypeChecker_Env.is_iface =
               (uu___54_298.FStar_TypeChecker_Env.is_iface);
             FStar_TypeChecker_Env.admit =
               (uu___54_298.FStar_TypeChecker_Env.admit);
             FStar_TypeChecker_Env.lax =
               (uu___54_298.FStar_TypeChecker_Env.lax);
             FStar_TypeChecker_Env.lax_universes =
               (uu___54_298.FStar_TypeChecker_Env.lax_universes);
             FStar_TypeChecker_Env.phase1 =
               (uu___54_298.FStar_TypeChecker_Env.phase1);
             FStar_TypeChecker_Env.failhard =
               (uu___54_298.FStar_TypeChecker_Env.failhard);
             FStar_TypeChecker_Env.nosynth =
               (uu___54_298.FStar_TypeChecker_Env.nosynth);
             FStar_TypeChecker_Env.uvar_subtyping =
               (uu___54_298.FStar_TypeChecker_Env.uvar_subtyping);
             FStar_TypeChecker_Env.tc_term =
               (uu___54_298.FStar_TypeChecker_Env.tc_term);
             FStar_TypeChecker_Env.type_of =
               (uu___54_298.FStar_TypeChecker_Env.type_of);
             FStar_TypeChecker_Env.universe_of =
               (uu___54_298.FStar_TypeChecker_Env.universe_of);
             FStar_TypeChecker_Env.check_type_of =
               (uu___54_298.FStar_TypeChecker_Env.check_type_of);
             FStar_TypeChecker_Env.use_bv_sorts =
               (uu___54_298.FStar_TypeChecker_Env.use_bv_sorts);
             FStar_TypeChecker_Env.qtbl_name_and_index =
               (uu___54_298.FStar_TypeChecker_Env.qtbl_name_and_index);
             FStar_TypeChecker_Env.normalized_eff_names =
               (uu___54_298.FStar_TypeChecker_Env.normalized_eff_names);
             FStar_TypeChecker_Env.fv_delta_depths =
               (uu___54_298.FStar_TypeChecker_Env.fv_delta_depths);
             FStar_TypeChecker_Env.proof_ns =
               (uu___54_298.FStar_TypeChecker_Env.proof_ns);
             FStar_TypeChecker_Env.synth_hook =
               (uu___54_298.FStar_TypeChecker_Env.synth_hook);
             FStar_TypeChecker_Env.try_solve_implicits_hook =
               (uu___54_298.FStar_TypeChecker_Env.try_solve_implicits_hook);
             FStar_TypeChecker_Env.splice =
               (uu___54_298.FStar_TypeChecker_Env.splice);
             FStar_TypeChecker_Env.mpreprocess =
               (uu___54_298.FStar_TypeChecker_Env.mpreprocess);
             FStar_TypeChecker_Env.postprocess =
               (uu___54_298.FStar_TypeChecker_Env.postprocess);
             FStar_TypeChecker_Env.identifier_info =
               (uu___54_298.FStar_TypeChecker_Env.identifier_info);
             FStar_TypeChecker_Env.tc_hooks =
               (uu___54_298.FStar_TypeChecker_Env.tc_hooks);
             FStar_TypeChecker_Env.dsenv =
               (uu___54_298.FStar_TypeChecker_Env.dsenv);
             FStar_TypeChecker_Env.nbe =
               (uu___54_298.FStar_TypeChecker_Env.nbe);
             FStar_TypeChecker_Env.strict_args_tab =
               (uu___54_298.FStar_TypeChecker_Env.strict_args_tab);
             FStar_TypeChecker_Env.erasable_types_tab =
               (uu___54_298.FStar_TypeChecker_Env.erasable_types_tab);
             FStar_TypeChecker_Env.enable_defer_to_tac =
               (uu___54_298.FStar_TypeChecker_Env.enable_defer_to_tac)
           } in
         match k with
         | FStar_Pervasives_Native.None ->
             let uu____299 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____305 =
               FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k1 in
             ())
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun quals ->
        (let uu____326 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffectsTc") in
         if uu____326
         then
           let uu____327 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____327
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____336 =
             let uu____341 =
               let uu____342 =
                 let uu____343 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 Prims.op_Hat uu____343 ")" in
               Prims.op_Hat "Binders are not supported for layered effects ("
                 uu____342 in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____341) in
           let uu____344 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
           FStar_Errors.raise_error uu____336 uu____344)
        else ();
        (let log_combinator s uu____368 =
           match uu____368 with
           | (us, t, ty) ->
               let uu____396 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffectsTc") in
               if uu____396
               then
                 let uu____397 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____398 = FStar_Syntax_Print.tscheme_to_string (us, t) in
                 let uu____403 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty) in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____397 s
                   uu____398 uu____403
               else () in
         let fresh_a_and_u_a a =
           let uu____423 = FStar_Syntax_Util.type_u () in
           FStar_All.pipe_right uu____423
             (fun uu____440 ->
                match uu____440 with
                | (t, u) ->
                    let uu____451 =
                      let uu____452 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t in
                      FStar_All.pipe_right uu____452
                        FStar_Syntax_Syntax.mk_binder in
                    (uu____451, u)) in
         let fresh_x_a x a =
           let uu____464 =
             let uu____465 =
               let uu____466 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst in
               FStar_All.pipe_right uu____466 FStar_Syntax_Syntax.bv_to_name in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____465 in
           FStar_All.pipe_right uu____464 FStar_Syntax_Syntax.mk_binder in
         let check_and_gen1 =
           let uu____498 =
             FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
           check_and_gen env0 uu____498 in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
           let uu____517 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature in
           match uu____517 with
           | (sig_us, sig_t, sig_ty) ->
               let uu____539 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
               (match uu____539 with
                | (us, t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                    let uu____559 = fresh_a_and_u_a "a" in
                    (match uu____559 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____579 =
                             let uu____580 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst in
                             FStar_All.pipe_right uu____580
                               FStar_Syntax_Syntax.bv_to_name in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____579 in
                         let bs = a :: rest_bs in
                         let k =
                           let uu____611 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff in
                           FStar_Syntax_Util.arrow bs uu____611 in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____616 =
                             let uu____619 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env) in
                             FStar_Syntax_Subst.close_univ_vars us uu____619 in
                           (sig_us, uu____616, sig_ty))))) in
         log_combinator "signature" signature;
         (let repr =
            let repr_ts =
              let uu____645 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              FStar_All.pipe_right uu____645 FStar_Util.must in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
            let uu____673 = check_and_gen1 "repr" Prims.int_one repr_ts in
            match uu____673 with
            | (repr_us, repr_t, repr_ty) ->
                let uu____695 =
                  FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                (match uu____695 with
                 | (us, ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                     let uu____715 = fresh_a_and_u_a "a" in
                     (match uu____715 with
                      | (a, u) ->
                          let rest_bs =
                            let signature_ts =
                              let uu____736 = signature in
                              match uu____736 with
                              | (us1, t, uu____751) -> (us1, t) in
                            let uu____768 =
                              let uu____769 =
                                FStar_All.pipe_right a
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____769
                                FStar_Syntax_Syntax.bv_to_name in
                            FStar_TypeChecker_Util.layered_effect_indices_as_binders
                              env r ed.FStar_Syntax_Syntax.mname signature_ts
                              u uu____768 in
                          let bs = a :: rest_bs in
                          let k =
                            let uu____796 =
                              let uu____799 = FStar_Syntax_Util.type_u () in
                              FStar_All.pipe_right uu____799
                                (fun uu____812 ->
                                   match uu____812 with
                                   | (t, u1) ->
                                       let uu____819 =
                                         let uu____822 =
                                           FStar_TypeChecker_Env.new_u_univ
                                             () in
                                         FStar_Pervasives_Native.Some
                                           uu____822 in
                                       FStar_Syntax_Syntax.mk_Total' t
                                         uu____819) in
                            FStar_Syntax_Util.arrow bs uu____796 in
                          let g = FStar_TypeChecker_Rel.teq env ty k in
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let uu____825 =
                              let uu____828 =
                                FStar_All.pipe_right k
                                  (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                     env) in
                              FStar_Syntax_Subst.close_univ_vars us uu____828 in
                            (repr_us, repr_t, uu____825))))) in
          log_combinator "repr" repr;
          (let fresh_repr r env u a_tm =
             let signature_ts =
               let uu____862 = signature in
               match uu____862 with | (us, t, uu____877) -> (us, t) in
             let repr_ts =
               let uu____895 = repr in
               match uu____895 with | (us, t, uu____910) -> (us, t) in
             FStar_TypeChecker_Util.fresh_effect_repr env r
               ed.FStar_Syntax_Syntax.mname signature_ts
               (FStar_Pervasives_Native.Some repr_ts) u a_tm in
           let not_an_arrow_error comb n t r =
             let uu____956 =
               let uu____961 =
                 let uu____962 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____963 = FStar_Util.string_of_int n in
                 let uu____964 = FStar_Syntax_Print.tag_of_term t in
                 let uu____965 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format5
                   "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                   uu____962 comb uu____963 uu____964 uu____965 in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____961) in
             FStar_Errors.raise_error uu____956 r in
           let return_repr =
             let return_repr_ts =
               let uu____992 =
                 FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
               FStar_All.pipe_right uu____992 FStar_Util.must in
             let r =
               (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
             let uu____1020 =
               check_and_gen1 "return_repr" Prims.int_one return_repr_ts in
             match uu____1020 with
             | (ret_us, ret_t, ret_ty) ->
                 let uu____1042 =
                   FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                 (match uu____1042 with
                  | (us, ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                      (check_no_subtyping_for_layered_combinator env ty
                         FStar_Pervasives_Native.None;
                       (let uu____1063 = fresh_a_and_u_a "a" in
                        match uu____1063 with
                        | (a, u_a) ->
                            let x_a = fresh_x_a "x" a in
                            let rest_bs =
                              let uu____1092 =
                                let uu____1093 =
                                  FStar_Syntax_Subst.compress ty in
                                uu____1093.FStar_Syntax_Syntax.n in
                              match uu____1092 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____1105)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____1132 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  (match uu____1132 with
                                   | (a', uu____1142)::(x', uu____1144)::bs1
                                       ->
                                       let uu____1174 =
                                         let uu____1175 =
                                           let uu____1180 =
                                             let uu____1183 =
                                               let uu____1184 =
                                                 let uu____1191 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a) in
                                                 (a', uu____1191) in
                                               FStar_Syntax_Syntax.NT
                                                 uu____1184 in
                                             [uu____1183] in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____1180 in
                                         FStar_All.pipe_right bs1 uu____1175 in
                                       let uu____1198 =
                                         let uu____1211 =
                                           let uu____1214 =
                                             let uu____1215 =
                                               let uu____1222 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      x_a) in
                                               (x', uu____1222) in
                                             FStar_Syntax_Syntax.NT
                                               uu____1215 in
                                           [uu____1214] in
                                         FStar_Syntax_Subst.subst_binders
                                           uu____1211 in
                                       FStar_All.pipe_right uu____1174
                                         uu____1198)
                              | uu____1237 ->
                                  not_an_arrow_error "return"
                                    (Prims.of_int (2)) ty r in
                            let bs = a :: x_a :: rest_bs in
                            let uu____1259 =
                              let uu____1264 =
                                FStar_TypeChecker_Env.push_binders env bs in
                              let uu____1265 =
                                FStar_All.pipe_right
                                  (FStar_Pervasives_Native.fst a)
                                  FStar_Syntax_Syntax.bv_to_name in
                              fresh_repr r uu____1264 u_a uu____1265 in
                            (match uu____1259 with
                             | (repr1, g) ->
                                 let k =
                                   let uu____1285 =
                                     FStar_Syntax_Syntax.mk_Total' repr1
                                       (FStar_Pervasives_Native.Some u_a) in
                                   FStar_Syntax_Util.arrow bs uu____1285 in
                                 let g_eq =
                                   FStar_TypeChecker_Rel.teq env ty k in
                                 ((let uu____1290 =
                                     FStar_TypeChecker_Env.conj_guard g g_eq in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env uu____1290);
                                  (let uu____1291 =
                                     let uu____1294 =
                                       FStar_All.pipe_right k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env) in
                                     FStar_All.pipe_right uu____1294
                                       (FStar_Syntax_Subst.close_univ_vars us) in
                                   (ret_us, ret_t, uu____1291))))))) in
           log_combinator "return_repr" return_repr;
           (let bind_repr =
              let bind_repr_ts =
                let uu____1322 =
                  FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                FStar_All.pipe_right uu____1322 FStar_Util.must in
              let r =
                (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
              let uu____1350 =
                check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
              match uu____1350 with
              | (bind_us, bind_t, bind_ty) ->
                  let uu____1372 =
                    FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                  (match uu____1372 with
                   | (us, ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                       (check_no_subtyping_for_layered_combinator env ty
                          FStar_Pervasives_Native.None;
                        (let uu____1393 = fresh_a_and_u_a "a" in
                         match uu____1393 with
                         | (a, u_a) ->
                             let uu____1412 = fresh_a_and_u_a "b" in
                             (match uu____1412 with
                              | (b, u_b) ->
                                  let rest_bs =
                                    let uu____1440 =
                                      let uu____1441 =
                                        FStar_Syntax_Subst.compress ty in
                                      uu____1441.FStar_Syntax_Syntax.n in
                                    match uu____1440 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____1453) when
                                        (FStar_List.length bs) >=
                                          (Prims.of_int (4))
                                        ->
                                        let uu____1480 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        (match uu____1480 with
                                         | (a', uu____1490)::(b', uu____1492)::bs1
                                             ->
                                             let uu____1522 =
                                               let uu____1523 =
                                                 FStar_All.pipe_right bs1
                                                   (FStar_List.splitAt
                                                      ((FStar_List.length bs1)
                                                         - (Prims.of_int (2)))) in
                                               FStar_All.pipe_right
                                                 uu____1523
                                                 FStar_Pervasives_Native.fst in
                                             let uu____1588 =
                                               let uu____1601 =
                                                 let uu____1604 =
                                                   let uu____1605 =
                                                     let uu____1612 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a) in
                                                     (a', uu____1612) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1605 in
                                                 let uu____1619 =
                                                   let uu____1622 =
                                                     let uu____1623 =
                                                       let uu____1630 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b) in
                                                       (b', uu____1630) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____1623 in
                                                   [uu____1622] in
                                                 uu____1604 :: uu____1619 in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1601 in
                                             FStar_All.pipe_right uu____1522
                                               uu____1588)
                                    | uu____1645 ->
                                        not_an_arrow_error "bind"
                                          (Prims.of_int (4)) ty r in
                                  let bs = a :: b :: rest_bs in
                                  let uu____1667 =
                                    let uu____1678 =
                                      let uu____1683 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____1684 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____1683 u_a uu____1684 in
                                    match uu____1678 with
                                    | (repr1, g) ->
                                        let uu____1699 =
                                          let uu____1706 =
                                            FStar_Syntax_Syntax.gen_bv "f"
                                              FStar_Pervasives_Native.None
                                              repr1 in
                                          FStar_All.pipe_right uu____1706
                                            FStar_Syntax_Syntax.mk_binder in
                                        (uu____1699, g) in
                                  (match uu____1667 with
                                   | (f, guard_f) ->
                                       let uu____1745 =
                                         let x_a = fresh_x_a "x" a in
                                         let uu____1757 =
                                           let uu____1762 =
                                             FStar_TypeChecker_Env.push_binders
                                               env
                                               (FStar_List.append bs [x_a]) in
                                           let uu____1781 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name in
                                           fresh_repr r uu____1762 u_b
                                             uu____1781 in
                                         match uu____1757 with
                                         | (repr1, g) ->
                                             let uu____1796 =
                                               let uu____1803 =
                                                 let uu____1804 =
                                                   let uu____1805 =
                                                     let uu____1808 =
                                                       let uu____1811 =
                                                         FStar_TypeChecker_Env.new_u_univ
                                                           () in
                                                       FStar_Pervasives_Native.Some
                                                         uu____1811 in
                                                     FStar_Syntax_Syntax.mk_Total'
                                                       repr1 uu____1808 in
                                                   FStar_Syntax_Util.arrow
                                                     [x_a] uu____1805 in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "g"
                                                   FStar_Pervasives_Native.None
                                                   uu____1804 in
                                               FStar_All.pipe_right
                                                 uu____1803
                                                 FStar_Syntax_Syntax.mk_binder in
                                             (uu____1796, g) in
                                       (match uu____1745 with
                                        | (g, guard_g) ->
                                            let uu____1862 =
                                              let uu____1867 =
                                                FStar_TypeChecker_Env.push_binders
                                                  env bs in
                                              let uu____1868 =
                                                FStar_All.pipe_right
                                                  (FStar_Pervasives_Native.fst
                                                     b)
                                                  FStar_Syntax_Syntax.bv_to_name in
                                              fresh_repr r uu____1867 u_b
                                                uu____1868 in
                                            (match uu____1862 with
                                             | (repr1, guard_repr) ->
                                                 let uu____1885 =
                                                   let uu____1890 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs in
                                                   let uu____1891 =
                                                     let uu____1892 =
                                                       FStar_Ident.string_of_lid
                                                         ed.FStar_Syntax_Syntax.mname in
                                                     FStar_Util.format1
                                                       "implicit for pure_wp in checking bind for %s"
                                                       uu____1892 in
                                                   pure_wp_uvar uu____1890
                                                     repr1 uu____1891 r in
                                                 (match uu____1885 with
                                                  | (pure_wp_uvar1,
                                                     g_pure_wp_uvar) ->
                                                      let k =
                                                        let uu____1910 =
                                                          let uu____1913 =
                                                            let uu____1914 =
                                                              let uu____1915
                                                                =
                                                                FStar_TypeChecker_Env.new_u_univ
                                                                  () in
                                                              [uu____1915] in
                                                            let uu____1916 =
                                                              let uu____1927
                                                                =
                                                                FStar_All.pipe_right
                                                                  pure_wp_uvar1
                                                                  FStar_Syntax_Syntax.as_arg in
                                                              [uu____1927] in
                                                            {
                                                              FStar_Syntax_Syntax.comp_univs
                                                                = uu____1914;
                                                              FStar_Syntax_Syntax.effect_name
                                                                =
                                                                FStar_Parser_Const.effect_PURE_lid;
                                                              FStar_Syntax_Syntax.result_typ
                                                                = repr1;
                                                              FStar_Syntax_Syntax.effect_args
                                                                = uu____1916;
                                                              FStar_Syntax_Syntax.flags
                                                                = []
                                                            } in
                                                          FStar_Syntax_Syntax.mk_Comp
                                                            uu____1913 in
                                                        FStar_Syntax_Util.arrow
                                                          (FStar_List.append
                                                             bs [f; g])
                                                          uu____1910 in
                                                      let guard_eq =
                                                        FStar_TypeChecker_Rel.teq
                                                          env ty k in
                                                      (FStar_List.iter
                                                         (FStar_TypeChecker_Rel.force_trivial_guard
                                                            env)
                                                         [guard_f;
                                                         guard_g;
                                                         guard_repr;
                                                         g_pure_wp_uvar;
                                                         guard_eq];
                                                       (let uu____1986 =
                                                          let uu____1989 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env) in
                                                          FStar_All.pipe_right
                                                            uu____1989
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               bind_us) in
                                                        (bind_us, bind_t,
                                                          uu____1986))))))))))) in
            log_combinator "bind_repr" bind_repr;
            (let stronger_repr =
               let stronger_repr =
                 let uu____2017 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_stronger_repr in
                 FStar_All.pipe_right uu____2017 FStar_Util.must in
               let r =
                 (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
               let uu____2045 =
                 check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
               match uu____2045 with
               | (stronger_us, stronger_t, stronger_ty) ->
                   ((let uu____2068 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                         (FStar_Options.Other "LayeredEffectsTc") in
                     if uu____2068
                     then
                       let uu____2069 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_t) in
                       let uu____2074 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_ty) in
                       FStar_Util.print2
                         "stronger combinator typechecked with term: %s and type: %s\n"
                         uu____2069 uu____2074
                     else ());
                    (let uu____2080 =
                       FStar_Syntax_Subst.open_univ_vars stronger_us
                         stronger_ty in
                     match uu____2080 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2101 = fresh_a_and_u_a "a" in
                           match uu____2101 with
                           | (a, u) ->
                               let rest_bs =
                                 let uu____2129 =
                                   let uu____2130 =
                                     FStar_Syntax_Subst.compress ty in
                                   uu____2130.FStar_Syntax_Syntax.n in
                                 match uu____2129 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs, uu____2142) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____2169 =
                                       FStar_Syntax_Subst.open_binders bs in
                                     (match uu____2169 with
                                      | (a', uu____2179)::bs1 ->
                                          let uu____2199 =
                                            let uu____2200 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one)) in
                                            FStar_All.pipe_right uu____2200
                                              FStar_Pervasives_Native.fst in
                                          let uu____2297 =
                                            let uu____2310 =
                                              let uu____2313 =
                                                let uu____2314 =
                                                  let uu____2321 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a) in
                                                  (a', uu____2321) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____2314 in
                                              [uu____2313] in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____2310 in
                                          FStar_All.pipe_right uu____2199
                                            uu____2297)
                                 | uu____2336 ->
                                     not_an_arrow_error "stronger"
                                       (Prims.of_int (2)) ty r in
                               let bs = a :: rest_bs in
                               let uu____2352 =
                                 let uu____2363 =
                                   let uu____2368 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs in
                                   let uu____2369 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name in
                                   fresh_repr r uu____2368 u uu____2369 in
                                 match uu____2363 with
                                 | (repr1, g) ->
                                     let uu____2384 =
                                       let uu____2391 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1 in
                                       FStar_All.pipe_right uu____2391
                                         FStar_Syntax_Syntax.mk_binder in
                                     (uu____2384, g) in
                               (match uu____2352 with
                                | (f, guard_f) ->
                                    let uu____2430 =
                                      let uu____2435 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____2436 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____2435 u uu____2436 in
                                    (match uu____2430 with
                                     | (ret_t, guard_ret_t) ->
                                         let uu____2453 =
                                           let uu____2458 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs in
                                           let uu____2459 =
                                             let uu____2460 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             FStar_Util.format1
                                               "implicit for pure_wp in checking stronger for %s"
                                               uu____2460 in
                                           pure_wp_uvar uu____2458 ret_t
                                             uu____2459 r in
                                         (match uu____2453 with
                                          | (pure_wp_uvar1, guard_wp) ->
                                              let c =
                                                let uu____2476 =
                                                  let uu____2477 =
                                                    let uu____2478 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        () in
                                                    [uu____2478] in
                                                  let uu____2479 =
                                                    let uu____2490 =
                                                      FStar_All.pipe_right
                                                        pure_wp_uvar1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____2490] in
                                                  {
                                                    FStar_Syntax_Syntax.comp_univs
                                                      = uu____2477;
                                                    FStar_Syntax_Syntax.effect_name
                                                      =
                                                      FStar_Parser_Const.effect_PURE_lid;
                                                    FStar_Syntax_Syntax.result_typ
                                                      = ret_t;
                                                    FStar_Syntax_Syntax.effect_args
                                                      = uu____2479;
                                                    FStar_Syntax_Syntax.flags
                                                      = []
                                                  } in
                                                FStar_Syntax_Syntax.mk_Comp
                                                  uu____2476 in
                                              let k =
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs [f])
                                                  c in
                                              ((let uu____2545 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "LayeredEffectsTc") in
                                                if uu____2545
                                                then
                                                  let uu____2546 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected type of subcomp before unification: %s\n"
                                                    uu____2546
                                                else ());
                                               (let guard_eq =
                                                  FStar_TypeChecker_Rel.teq
                                                    env ty k in
                                                FStar_List.iter
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env)
                                                  [guard_f;
                                                  guard_ret_t;
                                                  guard_wp;
                                                  guard_eq];
                                                (let uu____2550 =
                                                   let uu____2553 =
                                                     let uu____2554 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____2554
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   FStar_All.pipe_right
                                                     uu____2553
                                                     (FStar_Syntax_Subst.close_univ_vars
                                                        stronger_us) in
                                                 (stronger_us, stronger_t,
                                                   uu____2550))))))))))) in
             log_combinator "stronger_repr" stronger_repr;
             (let if_then_else =
                let if_then_else_ts =
                  let uu____2584 =
                    FStar_All.pipe_right ed
                      FStar_Syntax_Util.get_layered_if_then_else_combinator in
                  FStar_All.pipe_right uu____2584 FStar_Util.must in
                let r =
                  (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                let uu____2624 =
                  check_and_gen1 "if_then_else" Prims.int_one if_then_else_ts in
                match uu____2624 with
                | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                    let uu____2646 =
                      FStar_Syntax_Subst.open_univ_vars if_then_else_us
                        if_then_else_t in
                    (match uu____2646 with
                     | (us, t) ->
                         let uu____2665 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_ty in
                         (match uu____2665 with
                          | (uu____2682, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 t (FStar_Pervasives_Native.Some ty);
                               (let uu____2686 = fresh_a_and_u_a "a" in
                                match uu____2686 with
                                | (a, u_a) ->
                                    let rest_bs =
                                      let uu____2714 =
                                        let uu____2715 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____2715.FStar_Syntax_Syntax.n in
                                      match uu____2714 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____2727) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____2754 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____2754 with
                                           | (a', uu____2764)::bs1 ->
                                               let uu____2784 =
                                                 let uu____2785 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____2785
                                                   FStar_Pervasives_Native.fst in
                                               let uu____2882 =
                                                 let uu____2895 =
                                                   let uu____2898 =
                                                     let uu____2899 =
                                                       let uu____2906 =
                                                         let uu____2909 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____2909
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       (a', uu____2906) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2899 in
                                                   [uu____2898] in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2895 in
                                               FStar_All.pipe_right
                                                 uu____2784 uu____2882)
                                      | uu____2930 ->
                                          not_an_arrow_error "if_then_else"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: rest_bs in
                                    let uu____2946 =
                                      let uu____2957 =
                                        let uu____2962 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____2963 =
                                          let uu____2964 =
                                            FStar_All.pipe_right a
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____2964
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____2962 u_a
                                          uu____2963 in
                                      match uu____2957 with
                                      | (repr1, g) ->
                                          let uu____2985 =
                                            let uu____2992 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____2992
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____2985, g) in
                                    (match uu____2946 with
                                     | (f_bs, guard_f) ->
                                         let uu____3031 =
                                           let uu____3042 =
                                             let uu____3047 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3048 =
                                               let uu____3049 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst in
                                               FStar_All.pipe_right
                                                 uu____3049
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____3047 u_a
                                               uu____3048 in
                                           match uu____3042 with
                                           | (repr1, g) ->
                                               let uu____3070 =
                                                 let uu____3077 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____3077
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____3070, g) in
                                         (match uu____3031 with
                                          | (g_bs, guard_g) ->
                                              let p_b =
                                                let uu____3123 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "p"
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Util.ktype0 in
                                                FStar_All.pipe_right
                                                  uu____3123
                                                  FStar_Syntax_Syntax.mk_binder in
                                              let uu____3130 =
                                                let uu____3135 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [p_b]) in
                                                let uu____3154 =
                                                  let uu____3155 =
                                                    FStar_All.pipe_right a
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_All.pipe_right
                                                    uu____3155
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____3135 u_a
                                                  uu____3154 in
                                              (match uu____3130 with
                                               | (t_body, guard_body) ->
                                                   let k =
                                                     FStar_Syntax_Util.abs
                                                       (FStar_List.append bs
                                                          [f_bs; g_bs; p_b])
                                                       t_body
                                                       FStar_Pervasives_Native.None in
                                                   let guard_eq =
                                                     FStar_TypeChecker_Rel.teq
                                                       env t k in
                                                   (FStar_All.pipe_right
                                                      [guard_f;
                                                      guard_g;
                                                      guard_body;
                                                      guard_eq]
                                                      (FStar_List.iter
                                                         (FStar_TypeChecker_Rel.force_trivial_guard
                                                            env));
                                                    (let uu____3215 =
                                                       let uu____3218 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env) in
                                                       FStar_All.pipe_right
                                                         uu____3218
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            if_then_else_us) in
                                                     (if_then_else_us,
                                                       uu____3215,
                                                       if_then_else_ty)))))))))) in
              log_combinator "if_then_else" if_then_else;
              (let r =
                 let uu____3230 =
                   let uu____3233 =
                     let uu____3242 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_layered_if_then_else_combinator in
                     FStar_All.pipe_right uu____3242 FStar_Util.must in
                   FStar_All.pipe_right uu____3233
                     FStar_Pervasives_Native.snd in
                 uu____3230.FStar_Syntax_Syntax.pos in
               let binder_aq_to_arg_aq aq =
                 match aq with
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                     uu____3317) -> aq
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                     uu____3318) ->
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit false)
                 | uu____3319 -> FStar_Pervasives_Native.None in
               let uu____3322 = if_then_else in
               match uu____3322 with
               | (ite_us, ite_t, uu____3337) ->
                   let uu____3350 =
                     FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                   (match uu____3350 with
                    | (us, ite_t1) ->
                        let uu____3357 =
                          let uu____3372 =
                            let uu____3373 =
                              FStar_Syntax_Subst.compress ite_t1 in
                            uu____3373.FStar_Syntax_Syntax.n in
                          match uu____3372 with
                          | FStar_Syntax_Syntax.Tm_abs
                              (bs, uu____3391, uu____3392) ->
                              let bs1 = FStar_Syntax_Subst.open_binders bs in
                              let uu____3418 =
                                let uu____3431 =
                                  let uu____3436 =
                                    let uu____3439 =
                                      let uu____3448 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                (Prims.of_int (3)))) in
                                      FStar_All.pipe_right uu____3448
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____3439
                                      (FStar_List.map
                                         FStar_Pervasives_Native.fst) in
                                  FStar_All.pipe_right uu____3436
                                    (FStar_List.map
                                       FStar_Syntax_Syntax.bv_to_name) in
                                FStar_All.pipe_right uu____3431
                                  (fun l ->
                                     let uu____3603 = l in
                                     match uu____3603 with
                                     | f::g::p::[] -> (f, g, p)) in
                              (match uu____3418 with
                               | (f, g, p) ->
                                   let uu____3672 =
                                     let uu____3673 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     FStar_TypeChecker_Env.push_binders
                                       uu____3673 bs1 in
                                   let uu____3674 =
                                     let uu____3675 =
                                       FStar_All.pipe_right bs1
                                         (FStar_List.map
                                            (fun uu____3700 ->
                                               match uu____3700 with
                                               | (b, qual) ->
                                                   let uu____3719 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       b in
                                                   (uu____3719,
                                                     (binder_aq_to_arg_aq
                                                        qual)))) in
                                     FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                       uu____3675 r in
                                   (uu____3672, uu____3674, f, g, p))
                          | uu____3726 ->
                              failwith
                                "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                        (match uu____3357 with
                         | (env, ite_t_applied, f_t, g_t, p_t) ->
                             let uu____3754 =
                               let uu____3763 = stronger_repr in
                               match uu____3763 with
                               | (uu____3784, subcomp_t, subcomp_ty) ->
                                   let uu____3799 =
                                     FStar_Syntax_Subst.open_univ_vars us
                                       subcomp_t in
                                   (match uu____3799 with
                                    | (uu____3812, subcomp_t1) ->
                                        let uu____3814 =
                                          let uu____3825 =
                                            FStar_Syntax_Subst.open_univ_vars
                                              us subcomp_ty in
                                          match uu____3825 with
                                          | (uu____3840, subcomp_ty1) ->
                                              let uu____3842 =
                                                let uu____3843 =
                                                  FStar_Syntax_Subst.compress
                                                    subcomp_ty1 in
                                                uu____3843.FStar_Syntax_Syntax.n in
                                              (match uu____3842 with
                                               | FStar_Syntax_Syntax.Tm_arrow
                                                   (bs, uu____3857) ->
                                                   let uu____3878 =
                                                     FStar_All.pipe_right bs
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs)
                                                             - Prims.int_one)) in
                                                   (match uu____3878 with
                                                    | (bs_except_last,
                                                       last_b) ->
                                                        let uu____3983 =
                                                          FStar_All.pipe_right
                                                            bs_except_last
                                                            (FStar_List.map
                                                               FStar_Pervasives_Native.snd) in
                                                        let uu____4010 =
                                                          let uu____4013 =
                                                            FStar_All.pipe_right
                                                              last_b
                                                              FStar_List.hd in
                                                          FStar_All.pipe_right
                                                            uu____4013
                                                            FStar_Pervasives_Native.snd in
                                                        (uu____3983,
                                                          uu____4010))
                                               | uu____4056 ->
                                                   failwith
                                                     "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                        (match uu____3814 with
                                         | (aqs_except_last, last_aq) ->
                                             let uu____4089 =
                                               let uu____4100 =
                                                 FStar_All.pipe_right
                                                   aqs_except_last
                                                   (FStar_List.map
                                                      binder_aq_to_arg_aq) in
                                               let uu____4117 =
                                                 FStar_All.pipe_right last_aq
                                                   binder_aq_to_arg_aq in
                                               (uu____4100, uu____4117) in
                                             (match uu____4089 with
                                              | (aqs_except_last1, last_aq1)
                                                  ->
                                                  let aux t =
                                                    let tun_args =
                                                      FStar_All.pipe_right
                                                        aqs_except_last1
                                                        (FStar_List.map
                                                           (fun aq ->
                                                              (FStar_Syntax_Syntax.tun,
                                                                aq))) in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      subcomp_t1
                                                      (FStar_List.append
                                                         tun_args
                                                         [(t, last_aq1)]) r in
                                                  let uu____4229 = aux f_t in
                                                  let uu____4232 = aux g_t in
                                                  (uu____4229, uu____4232)))) in
                             (match uu____3754 with
                              | (subcomp_f, subcomp_g) ->
                                  let uu____4249 =
                                    let aux t =
                                      let uu____4266 =
                                        let uu____4267 =
                                          let uu____4294 =
                                            let uu____4311 =
                                              let uu____4320 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  ite_t_applied in
                                              FStar_Util.Inr uu____4320 in
                                            (uu____4311,
                                              FStar_Pervasives_Native.None) in
                                          (t, uu____4294,
                                            FStar_Pervasives_Native.None) in
                                        FStar_Syntax_Syntax.Tm_ascribed
                                          uu____4267 in
                                      FStar_Syntax_Syntax.mk uu____4266 r in
                                    let uu____4361 = aux subcomp_f in
                                    let uu____4362 = aux subcomp_g in
                                    (uu____4361, uu____4362) in
                                  (match uu____4249 with
                                   | (tm_subcomp_ascribed_f,
                                      tm_subcomp_ascribed_g) ->
                                       ((let uu____4366 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____4366
                                         then
                                           let uu____4367 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_f in
                                           let uu____4368 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_g in
                                           FStar_Util.print2
                                             "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                             uu____4367 uu____4368
                                         else ());
                                        (let uu____4370 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env tm_subcomp_ascribed_f in
                                         match uu____4370 with
                                         | (uu____4377, uu____4378, g_f) ->
                                             let g_f1 =
                                               let uu____4381 =
                                                 FStar_TypeChecker_Env.guard_of_guard_formula
                                                   (FStar_TypeChecker_Common.NonTrivial
                                                      p_t) in
                                               FStar_TypeChecker_Env.imp_guard
                                                 uu____4381 g_f in
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env g_f1;
                                              (let uu____4383 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env tm_subcomp_ascribed_g in
                                               match uu____4383 with
                                               | (uu____4390, uu____4391,
                                                  g_g) ->
                                                   let g_g1 =
                                                     let not_p =
                                                       let uu____4395 =
                                                         let uu____4396 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             FStar_Parser_Const.not_lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             FStar_Pervasives_Native.None in
                                                         FStar_All.pipe_right
                                                           uu____4396
                                                           FStar_Syntax_Syntax.fv_to_tm in
                                                       let uu____4397 =
                                                         let uu____4398 =
                                                           FStar_All.pipe_right
                                                             p_t
                                                             FStar_Syntax_Syntax.as_arg in
                                                         [uu____4398] in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____4395
                                                         uu____4397 r in
                                                     let uu____4431 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         (FStar_TypeChecker_Common.NonTrivial
                                                            not_p) in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____4431 g_g in
                                                   FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_g1)))))))));
              (let tc_action env act =
                 let env01 = env in
                 let r =
                   (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                 if
                   (FStar_List.length act.FStar_Syntax_Syntax.action_params)
                     <> Prims.int_zero
                 then
                   (let uu____4452 =
                      let uu____4457 =
                        let uu____4458 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____4459 =
                          FStar_Ident.string_of_lid
                            act.FStar_Syntax_Syntax.action_name in
                        let uu____4460 =
                          FStar_Syntax_Print.binders_to_string "; "
                            act.FStar_Syntax_Syntax.action_params in
                        FStar_Util.format3
                          "Action %s:%s has non-empty action params (%s)"
                          uu____4458 uu____4459 uu____4460 in
                      (FStar_Errors.Fatal_MalformedActionDeclaration,
                        uu____4457) in
                    FStar_Errors.raise_error uu____4452 r)
                 else ();
                 (let uu____4462 =
                    let uu____4467 =
                      FStar_Syntax_Subst.univ_var_opening
                        act.FStar_Syntax_Syntax.action_univs in
                    match uu____4467 with
                    | (usubst, us) ->
                        let uu____4490 =
                          FStar_TypeChecker_Env.push_univ_vars env us in
                        let uu____4491 =
                          let uu___450_4492 = act in
                          let uu____4493 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_defn in
                          let uu____4494 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_typ in
                          {
                            FStar_Syntax_Syntax.action_name =
                              (uu___450_4492.FStar_Syntax_Syntax.action_name);
                            FStar_Syntax_Syntax.action_unqualified_name =
                              (uu___450_4492.FStar_Syntax_Syntax.action_unqualified_name);
                            FStar_Syntax_Syntax.action_univs = us;
                            FStar_Syntax_Syntax.action_params =
                              (uu___450_4492.FStar_Syntax_Syntax.action_params);
                            FStar_Syntax_Syntax.action_defn = uu____4493;
                            FStar_Syntax_Syntax.action_typ = uu____4494
                          } in
                        (uu____4490, uu____4491) in
                  match uu____4462 with
                  | (env1, act1) ->
                      let act_typ =
                        let uu____4498 =
                          let uu____4499 =
                            FStar_Syntax_Subst.compress
                              act1.FStar_Syntax_Syntax.action_typ in
                          uu____4499.FStar_Syntax_Syntax.n in
                        match uu____4498 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                            let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                            let uu____4525 =
                              FStar_Ident.lid_equals
                                ct.FStar_Syntax_Syntax.effect_name
                                ed.FStar_Syntax_Syntax.mname in
                            if uu____4525
                            then
                              let repr_ts =
                                let uu____4527 = repr in
                                match uu____4527 with
                                | (us, t, uu____4542) -> (us, t) in
                              let repr1 =
                                let uu____4560 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts ct.FStar_Syntax_Syntax.comp_univs in
                                FStar_All.pipe_right uu____4560
                                  FStar_Pervasives_Native.snd in
                              let repr2 =
                                let uu____4570 =
                                  let uu____4571 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ in
                                  uu____4571 ::
                                    (ct.FStar_Syntax_Syntax.effect_args) in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____4570 r in
                              let c1 =
                                let uu____4589 =
                                  let uu____4592 =
                                    FStar_TypeChecker_Env.new_u_univ () in
                                  FStar_Pervasives_Native.Some uu____4592 in
                                FStar_Syntax_Syntax.mk_Total' repr2
                                  uu____4589 in
                              FStar_Syntax_Util.arrow bs c1
                            else act1.FStar_Syntax_Syntax.action_typ
                        | uu____4594 -> act1.FStar_Syntax_Syntax.action_typ in
                      let uu____4595 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          act_typ in
                      (match uu____4595 with
                       | (act_typ1, uu____4603, g_t) ->
                           let uu____4605 =
                             let uu____4612 =
                               let uu___475_4613 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   act_typ1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___475_4613.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___475_4613.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___475_4613.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___475_4613.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___475_4613.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___475_4613.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___475_4613.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___475_4613.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___475_4613.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___475_4613.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   false;
                                 FStar_TypeChecker_Env.effects =
                                   (uu___475_4613.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___475_4613.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___475_4613.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___475_4613.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___475_4613.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___475_4613.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___475_4613.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___475_4613.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___475_4613.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___475_4613.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___475_4613.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___475_4613.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___475_4613.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___475_4613.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___475_4613.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___475_4613.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___475_4613.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___475_4613.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___475_4613.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___475_4613.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___475_4613.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___475_4613.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___475_4613.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___475_4613.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___475_4613.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___475_4613.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___475_4613.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___475_4613.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___475_4613.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___475_4613.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___475_4613.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___475_4613.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___475_4613.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___475_4613.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___475_4613.FStar_TypeChecker_Env.erasable_types_tab);
                                 FStar_TypeChecker_Env.enable_defer_to_tac =
                                   (uu___475_4613.FStar_TypeChecker_Env.enable_defer_to_tac)
                               } in
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu____4612
                               act1.FStar_Syntax_Syntax.action_defn in
                           (match uu____4605 with
                            | (act_defn, uu____4615, g_d) ->
                                ((let uu____4618 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "LayeredEffectsTc") in
                                  if uu____4618
                                  then
                                    let uu____4619 =
                                      FStar_Syntax_Print.term_to_string
                                        act_defn in
                                    let uu____4620 =
                                      FStar_Syntax_Print.term_to_string
                                        act_typ1 in
                                    FStar_Util.print2
                                      "Typechecked action definition: %s and action type: %s\n"
                                      uu____4619 uu____4620
                                  else ());
                                 (let uu____4622 =
                                    let act_typ2 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        act_typ1 in
                                    let uu____4630 =
                                      let uu____4631 =
                                        FStar_Syntax_Subst.compress act_typ2 in
                                      uu____4631.FStar_Syntax_Syntax.n in
                                    match uu____4630 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____4641) ->
                                        let bs1 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        let env2 =
                                          FStar_TypeChecker_Env.push_binders
                                            env1 bs1 in
                                        let uu____4664 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____4664 with
                                         | (t, u) ->
                                             let reason =
                                               let uu____4678 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____4679 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               FStar_Util.format2
                                                 "implicit for return type of action %s:%s"
                                                 uu____4678 uu____4679 in
                                             let uu____4680 =
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r env2 t in
                                             (match uu____4680 with
                                              | (a_tm, uu____4700, g_tm) ->
                                                  let uu____4714 =
                                                    fresh_repr r env2 u a_tm in
                                                  (match uu____4714 with
                                                   | (repr1, g) ->
                                                       let uu____4727 =
                                                         let uu____4730 =
                                                           let uu____4733 =
                                                             let uu____4736 =
                                                               FStar_TypeChecker_Env.new_u_univ
                                                                 () in
                                                             FStar_All.pipe_right
                                                               uu____4736
                                                               (fun
                                                                  uu____4739
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____4739) in
                                                           FStar_Syntax_Syntax.mk_Total'
                                                             repr1 uu____4733 in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____4730 in
                                                       let uu____4740 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g g_tm in
                                                       (uu____4727,
                                                         uu____4740))))
                                    | uu____4743 ->
                                        let uu____4744 =
                                          let uu____4749 =
                                            let uu____4750 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____4751 =
                                              FStar_Ident.string_of_lid
                                                act1.FStar_Syntax_Syntax.action_name in
                                            let uu____4752 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.format3
                                              "Unexpected non-function type for action %s:%s (%s)"
                                              uu____4750 uu____4751
                                              uu____4752 in
                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                            uu____4749) in
                                        FStar_Errors.raise_error uu____4744 r in
                                  match uu____4622 with
                                  | (k, g_k) ->
                                      ((let uu____4766 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsTc") in
                                        if uu____4766
                                        then
                                          let uu____4767 =
                                            FStar_Syntax_Print.term_to_string
                                              k in
                                          FStar_Util.print1
                                            "Expected action type: %s\n"
                                            uu____4767
                                        else ());
                                       (let g =
                                          FStar_TypeChecker_Rel.teq env1
                                            act_typ1 k in
                                        FStar_List.iter
                                          (FStar_TypeChecker_Rel.force_trivial_guard
                                             env1) [g_t; g_d; g_k; g];
                                        (let uu____4772 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____4772
                                         then
                                           let uu____4773 =
                                             FStar_Syntax_Print.term_to_string
                                               k in
                                           FStar_Util.print1
                                             "Expected action type after unification: %s\n"
                                             uu____4773
                                         else ());
                                        (let act_typ2 =
                                           let err_msg t =
                                             let uu____4782 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             let uu____4783 =
                                               FStar_Ident.string_of_lid
                                                 act1.FStar_Syntax_Syntax.action_name in
                                             let uu____4784 =
                                               FStar_Syntax_Print.term_to_string
                                                 t in
                                             FStar_Util.format3
                                               "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                               uu____4782 uu____4783
                                               uu____4784 in
                                           let repr_args t =
                                             let uu____4803 =
                                               let uu____4804 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____4804.FStar_Syntax_Syntax.n in
                                             match uu____4803 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (head, a::is) ->
                                                 let uu____4856 =
                                                   let uu____4857 =
                                                     FStar_Syntax_Subst.compress
                                                       head in
                                                   uu____4857.FStar_Syntax_Syntax.n in
                                                 (match uu____4856 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      (uu____4866, us) ->
                                                      (us,
                                                        (FStar_Pervasives_Native.fst
                                                           a), is)
                                                  | uu____4876 ->
                                                      let uu____4877 =
                                                        let uu____4882 =
                                                          err_msg t in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4882) in
                                                      FStar_Errors.raise_error
                                                        uu____4877 r)
                                             | uu____4889 ->
                                                 let uu____4890 =
                                                   let uu____4895 = err_msg t in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____4895) in
                                                 FStar_Errors.raise_error
                                                   uu____4890 r in
                                           let k1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 k in
                                           let uu____4903 =
                                             let uu____4904 =
                                               FStar_Syntax_Subst.compress k1 in
                                             uu____4904.FStar_Syntax_Syntax.n in
                                           match uu____4903 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, c) ->
                                               let uu____4929 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs c in
                                               (match uu____4929 with
                                                | (bs1, c1) ->
                                                    let uu____4936 =
                                                      repr_args
                                                        (FStar_Syntax_Util.comp_result
                                                           c1) in
                                                    (match uu____4936 with
                                                     | (us, a, is) ->
                                                         let ct =
                                                           {
                                                             FStar_Syntax_Syntax.comp_univs
                                                               = us;
                                                             FStar_Syntax_Syntax.effect_name
                                                               =
                                                               (ed.FStar_Syntax_Syntax.mname);
                                                             FStar_Syntax_Syntax.result_typ
                                                               = a;
                                                             FStar_Syntax_Syntax.effect_args
                                                               = is;
                                                             FStar_Syntax_Syntax.flags
                                                               = []
                                                           } in
                                                         let uu____4947 =
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             ct in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____4947))
                                           | uu____4950 ->
                                               let uu____4951 =
                                                 let uu____4956 = err_msg k1 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____4956) in
                                               FStar_Errors.raise_error
                                                 uu____4951 r in
                                         (let uu____4958 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____4958
                                          then
                                            let uu____4959 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.print1
                                              "Action type after injecting it into the monad: %s\n"
                                              uu____4959
                                          else ());
                                         (let act2 =
                                            let uu____4962 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env1 act_defn in
                                            match uu____4962 with
                                            | (us, act_defn1) ->
                                                if
                                                  act1.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then
                                                  let uu___548_4975 = act1 in
                                                  let uu____4976 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      us act_typ2 in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___548_4975.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___548_4975.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      = us;
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___548_4975.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____4976
                                                  }
                                                else
                                                  (let uu____4978 =
                                                     ((FStar_List.length us)
                                                        =
                                                        (FStar_List.length
                                                           act1.FStar_Syntax_Syntax.action_univs))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1 ->
                                                             fun u2 ->
                                                               let uu____4984
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2 in
                                                               uu____4984 =
                                                                 Prims.int_zero)
                                                          us
                                                          act1.FStar_Syntax_Syntax.action_univs) in
                                                   if uu____4978
                                                   then
                                                     let uu___553_4985 = act1 in
                                                     let uu____4986 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                         act_typ2 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___553_4985.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___553_4985.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         =
                                                         (uu___553_4985.FStar_Syntax_Syntax.action_univs);
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___553_4985.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = act_defn1;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____4986
                                                     }
                                                   else
                                                     (let uu____4988 =
                                                        let uu____4993 =
                                                          let uu____4994 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname in
                                                          let uu____4995 =
                                                            FStar_Ident.string_of_lid
                                                              act1.FStar_Syntax_Syntax.action_name in
                                                          let uu____4996 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              us in
                                                          let uu____4997 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              act1.FStar_Syntax_Syntax.action_univs in
                                                          FStar_Util.format4
                                                            "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                            uu____4994
                                                            uu____4995
                                                            uu____4996
                                                            uu____4997 in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____4993) in
                                                      FStar_Errors.raise_error
                                                        uu____4988 r)) in
                                          act2))))))))) in
               let tschemes_of uu____5019 =
                 match uu____5019 with | (us, t, ty) -> ((us, t), (us, ty)) in
               let combinators =
                 let uu____5064 =
                   let uu____5065 = tschemes_of repr in
                   let uu____5070 = tschemes_of return_repr in
                   let uu____5075 = tschemes_of bind_repr in
                   let uu____5080 = tschemes_of stronger_repr in
                   let uu____5085 = tschemes_of if_then_else in
                   {
                     FStar_Syntax_Syntax.l_repr = uu____5065;
                     FStar_Syntax_Syntax.l_return = uu____5070;
                     FStar_Syntax_Syntax.l_bind = uu____5075;
                     FStar_Syntax_Syntax.l_subcomp = uu____5080;
                     FStar_Syntax_Syntax.l_if_then_else = uu____5085
                   } in
                 FStar_Syntax_Syntax.Layered_eff uu____5064 in
               let uu___562_5090 = ed in
               let uu____5091 =
                 FStar_List.map (tc_action env0)
                   ed.FStar_Syntax_Syntax.actions in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___562_5090.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___562_5090.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs =
                   (uu___562_5090.FStar_Syntax_Syntax.univs);
                 FStar_Syntax_Syntax.binders =
                   (uu___562_5090.FStar_Syntax_Syntax.binders);
                 FStar_Syntax_Syntax.signature =
                   (let uu____5098 = signature in
                    match uu____5098 with | (us, t, uu____5113) -> (us, t));
                 FStar_Syntax_Syntax.combinators = combinators;
                 FStar_Syntax_Syntax.actions = uu____5091;
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___562_5090.FStar_Syntax_Syntax.eff_attrs)
               })))))))
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun _quals ->
        (let uu____5150 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED") in
         if uu____5150
         then
           let uu____5151 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5151
         else ());
        (let uu____5153 =
           let uu____5158 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
           match uu____5158 with
           | (ed_univs_subst, ed_univs) ->
               let bs =
                 let uu____5182 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders in
                 FStar_Syntax_Subst.open_binders uu____5182 in
               let uu____5183 =
                 let uu____5190 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5190 bs in
               (match uu____5183 with
                | (bs1, uu____5196, uu____5197) ->
                    let uu____5198 =
                      let tmp_t =
                        let uu____5208 =
                          let uu____5211 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5216 ->
                                 FStar_Pervasives_Native.Some uu____5216) in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5211 in
                        FStar_Syntax_Util.arrow bs1 uu____5208 in
                      let uu____5217 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t in
                      match uu____5217 with
                      | (us, tmp_t1) ->
                          let uu____5234 =
                            let uu____5235 =
                              let uu____5236 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals in
                              FStar_All.pipe_right uu____5236
                                FStar_Pervasives_Native.fst in
                            FStar_All.pipe_right uu____5235
                              FStar_Syntax_Subst.close_binders in
                          (us, uu____5234) in
                    (match uu____5198 with
                     | (us, bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5273 ->
                              let uu____5276 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1 ->
                                        fun u2 ->
                                          let uu____5282 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2 in
                                          uu____5282 = Prims.int_zero)
                                     ed_univs us) in
                              if uu____5276
                              then (us, bs2)
                              else
                                (let uu____5288 =
                                   let uu____5293 =
                                     let uu____5294 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname in
                                     let uu____5295 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs) in
                                     let uu____5296 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us) in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5294 uu____5295 uu____5296 in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5293) in
                                 let uu____5297 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Errors.raise_error uu____5288
                                   uu____5297)))) in
         match uu____5153 with
         | (us, bs) ->
             let ed1 =
               let uu___596_5305 = ed in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___596_5305.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___596_5305.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___596_5305.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___596_5305.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___596_5305.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___596_5305.FStar_Syntax_Syntax.eff_attrs)
               } in
             let uu____5306 = FStar_Syntax_Subst.univ_var_opening us in
             (match uu____5306 with
              | (ed_univs_subst, ed_univs) ->
                  let uu____5325 =
                    let uu____5330 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                    FStar_Syntax_Subst.open_binders' uu____5330 in
                  (match uu____5325 with
                   | (ed_bs, ed_bs_subst) ->
                       let ed2 =
                         let op uu____5351 =
                           match uu____5351 with
                           | (us1, t) ->
                               let t1 =
                                 let uu____5371 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst in
                                 FStar_Syntax_Subst.subst uu____5371 t in
                               let uu____5380 =
                                 let uu____5381 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst in
                                 FStar_Syntax_Subst.subst uu____5381 t1 in
                               (us1, uu____5380) in
                         let uu___610_5386 = ed1 in
                         let uu____5387 =
                           op ed1.FStar_Syntax_Syntax.signature in
                         let uu____5388 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators in
                         let uu____5389 =
                           FStar_List.map
                             (fun a ->
                                let uu___613_5397 = a in
                                let uu____5398 =
                                  let uu____5399 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn)) in
                                  FStar_Pervasives_Native.snd uu____5399 in
                                let uu____5410 =
                                  let uu____5411 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ)) in
                                  FStar_Pervasives_Native.snd uu____5411 in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___613_5397.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___613_5397.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___613_5397.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___613_5397.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5398;
                                  FStar_Syntax_Syntax.action_typ = uu____5410
                                }) ed1.FStar_Syntax_Syntax.actions in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___610_5386.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___610_5386.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___610_5386.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___610_5386.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5387;
                           FStar_Syntax_Syntax.combinators = uu____5388;
                           FStar_Syntax_Syntax.actions = uu____5389;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___610_5386.FStar_Syntax_Syntax.eff_attrs)
                         } in
                       ((let uu____5423 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED") in
                         if uu____5423
                         then
                           let uu____5424 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2 in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5424
                         else ());
                        (let env =
                           let uu____5427 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs in
                           FStar_TypeChecker_Env.push_binders uu____5427
                             ed_bs in
                         let check_and_gen' comb n env_opt uu____5460 k =
                           match uu____5460 with
                           | (us1, t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env in
                               let uu____5476 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t in
                               (match uu____5476 with
                                | (us2, t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5485 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2 in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5485 t1 k1
                                      | FStar_Pervasives_Native.None ->
                                          let uu____5486 =
                                            let uu____5493 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5493 t1 in
                                          (match uu____5486 with
                                           | (t2, uu____5495, g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2)) in
                                    let uu____5498 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2 in
                                    (match uu____5498 with
                                     | (g_us, t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5511 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname in
                                               let uu____5512 =
                                                 FStar_Util.string_of_int n in
                                               let uu____5513 =
                                                 let uu____5514 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length in
                                                 FStar_All.pipe_right
                                                   uu____5514
                                                   FStar_Util.string_of_int in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5511 comb uu____5512
                                                 uu____5513 in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5522 ->
                                               let uu____5523 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____5529 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____5529 =
                                                             Prims.int_zero)
                                                      us2 g_us) in
                                               if uu____5523
                                               then (g_us, t3)
                                               else
                                                 (let uu____5535 =
                                                    let uu____5540 =
                                                      let uu____5541 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____5542 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2) in
                                                      let uu____5543 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us) in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5541 comb
                                                        uu____5542 uu____5543 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5540) in
                                                  FStar_Errors.raise_error
                                                    uu____5535
                                                    t3.FStar_Syntax_Syntax.pos))))) in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None in
                         (let uu____5546 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED") in
                          if uu____5546
                          then
                            let uu____5547 =
                              FStar_Syntax_Print.tscheme_to_string signature in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5547
                          else ());
                         (let fresh_a_and_wp uu____5560 =
                            let fail t =
                              let uu____5573 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t in
                              FStar_Errors.raise_error uu____5573
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                            let uu____5588 =
                              FStar_TypeChecker_Env.inst_tscheme signature in
                            match uu____5588 with
                            | (uu____5599, signature1) ->
                                let uu____5601 =
                                  let uu____5602 =
                                    FStar_Syntax_Subst.compress signature1 in
                                  uu____5602.FStar_Syntax_Syntax.n in
                                (match uu____5601 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1, uu____5612) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1 in
                                     (match bs2 with
                                      | (a, uu____5641)::(wp, uu____5643)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5672 -> fail signature1)
                                 | uu____5673 -> fail signature1) in
                          let log_combinator s ts =
                            let uu____5685 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED") in
                            if uu____5685
                            then
                              let uu____5686 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname in
                              let uu____5687 =
                                FStar_Syntax_Print.tscheme_to_string ts in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____5686 s uu____5687
                            else () in
                          let ret_wp =
                            let uu____5690 = fresh_a_and_wp () in
                            match uu____5690 with
                            | (a, wp_sort) ->
                                let k =
                                  let uu____5706 =
                                    let uu____5715 =
                                      FStar_Syntax_Syntax.mk_binder a in
                                    let uu____5722 =
                                      let uu____5731 =
                                        let uu____5738 =
                                          FStar_Syntax_Syntax.bv_to_name a in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5738 in
                                      [uu____5731] in
                                    uu____5715 :: uu____5722 in
                                  let uu____5757 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                  FStar_Syntax_Util.arrow uu____5706
                                    uu____5757 in
                                let uu____5760 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5760
                                  (FStar_Pervasives_Native.Some k) in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5771 = fresh_a_and_wp () in
                             match uu____5771 with
                             | (a, wp_sort_a) ->
                                 let uu____5784 = fresh_a_and_wp () in
                                 (match uu____5784 with
                                  | (b, wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5800 =
                                          let uu____5809 =
                                            let uu____5816 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5816 in
                                          [uu____5809] in
                                        let uu____5829 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____5800
                                          uu____5829 in
                                      let k =
                                        let uu____5835 =
                                          let uu____5844 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____5851 =
                                            let uu____5860 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____5867 =
                                              let uu____5876 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____5883 =
                                                let uu____5892 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a in
                                                let uu____5899 =
                                                  let uu____5908 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b in
                                                  [uu____5908] in
                                                uu____5892 :: uu____5899 in
                                              uu____5876 :: uu____5883 in
                                            uu____5860 :: uu____5867 in
                                          uu____5844 :: uu____5851 in
                                        let uu____5951 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____5835
                                          uu____5951 in
                                      let uu____5954 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____5954
                                        (FStar_Pervasives_Native.Some k)) in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____5965 = fresh_a_and_wp () in
                              match uu____5965 with
                              | (a, wp_sort_a) ->
                                  let uu____5978 =
                                    FStar_Syntax_Util.type_u () in
                                  (match uu____5978 with
                                   | (t, uu____5984) ->
                                       let k =
                                         let uu____5988 =
                                           let uu____5997 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____6004 =
                                             let uu____6013 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____6020 =
                                               let uu____6029 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____6029] in
                                             uu____6013 :: uu____6020 in
                                           uu____5997 :: uu____6004 in
                                         let uu____6060 =
                                           FStar_Syntax_Syntax.mk_Total t in
                                         FStar_Syntax_Util.arrow uu____5988
                                           uu____6060 in
                                       let uu____6063 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6063
                                         (FStar_Pervasives_Native.Some k)) in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6074 = fresh_a_and_wp () in
                               match uu____6074 with
                               | (a, wp_sort_a) ->
                                   let p =
                                     let uu____6088 =
                                       let uu____6091 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname in
                                       FStar_Pervasives_Native.Some
                                         uu____6091 in
                                     let uu____6092 =
                                       let uu____6093 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____6093
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.new_bv uu____6088
                                       uu____6092 in
                                   let k =
                                     let uu____6105 =
                                       let uu____6114 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____6121 =
                                         let uu____6130 =
                                           FStar_Syntax_Syntax.mk_binder p in
                                         let uu____6137 =
                                           let uu____6146 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a in
                                           let uu____6153 =
                                             let uu____6162 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             [uu____6162] in
                                           uu____6146 :: uu____6153 in
                                         uu____6130 :: uu____6137 in
                                       uu____6114 :: uu____6121 in
                                     let uu____6199 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a in
                                     FStar_Syntax_Util.arrow uu____6105
                                       uu____6199 in
                                   let uu____6202 =
                                     let uu____6207 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                     FStar_All.pipe_right uu____6207
                                       FStar_Util.must in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6202
                                     (FStar_Pervasives_Native.Some k) in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6236 = fresh_a_and_wp () in
                                match uu____6236 with
                                | (a, wp_sort_a) ->
                                    let k =
                                      let uu____6252 =
                                        let uu____6261 =
                                          FStar_Syntax_Syntax.mk_binder a in
                                        let uu____6268 =
                                          let uu____6277 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a in
                                          [uu____6277] in
                                        uu____6261 :: uu____6268 in
                                      let uu____6302 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a in
                                      FStar_Syntax_Util.arrow uu____6252
                                        uu____6302 in
                                    let uu____6305 =
                                      let uu____6310 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator in
                                      FStar_All.pipe_right uu____6310
                                        FStar_Util.must in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6305
                                      (FStar_Pervasives_Native.Some k) in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6323 = fresh_a_and_wp () in
                                 match uu____6323 with
                                 | (a, wp_sort_a) ->
                                     let b =
                                       let uu____6337 =
                                         let uu____6340 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____6340 in
                                       let uu____6341 =
                                         let uu____6342 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____6342
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____6337
                                         uu____6341 in
                                     let wp_sort_b_a =
                                       let uu____6354 =
                                         let uu____6363 =
                                           let uu____6370 =
                                             FStar_Syntax_Syntax.bv_to_name b in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6370 in
                                         [uu____6363] in
                                       let uu____6383 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____6354
                                         uu____6383 in
                                     let k =
                                       let uu____6389 =
                                         let uu____6398 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____6405 =
                                           let uu____6414 =
                                             FStar_Syntax_Syntax.mk_binder b in
                                           let uu____6421 =
                                             let uu____6430 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a in
                                             [uu____6430] in
                                           uu____6414 :: uu____6421 in
                                         uu____6398 :: uu____6405 in
                                       let uu____6461 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____6389
                                         uu____6461 in
                                     let uu____6464 =
                                       let uu____6469 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator in
                                       FStar_All.pipe_right uu____6469
                                         FStar_Util.must in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6464
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6482 = fresh_a_and_wp () in
                                  match uu____6482 with
                                  | (a, wp_sort_a) ->
                                      let uu____6495 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____6495 with
                                       | (t, uu____6501) ->
                                           let k =
                                             let uu____6505 =
                                               let uu____6514 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____6521 =
                                                 let uu____6530 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____6530] in
                                               uu____6514 :: uu____6521 in
                                             let uu____6555 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t in
                                             FStar_Syntax_Util.arrow
                                               uu____6505 uu____6555 in
                                           let trivial =
                                             let uu____6559 =
                                               let uu____6564 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator in
                                               FStar_All.pipe_right
                                                 uu____6564 FStar_Util.must in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6559
                                               (FStar_Pervasives_Native.Some
                                                  k) in
                                           (log_combinator "trivial" trivial;
                                            trivial)) in
                                let uu____6576 =
                                  let uu____6593 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr in
                                  match uu____6593 with
                                  | FStar_Pervasives_Native.None ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6622 ->
                                      let repr =
                                        let uu____6626 = fresh_a_and_wp () in
                                        match uu____6626 with
                                        | (a, wp_sort_a) ->
                                            let uu____6639 =
                                              FStar_Syntax_Util.type_u () in
                                            (match uu____6639 with
                                             | (t, uu____6645) ->
                                                 let k =
                                                   let uu____6649 =
                                                     let uu____6658 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a in
                                                     let uu____6665 =
                                                       let uu____6674 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       [uu____6674] in
                                                     uu____6658 :: uu____6665 in
                                                   let uu____6699 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6649 uu____6699 in
                                                 let uu____6702 =
                                                   let uu____6707 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr in
                                                   FStar_All.pipe_right
                                                     uu____6707
                                                     FStar_Util.must in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6702
                                                   (FStar_Pervasives_Native.Some
                                                      k)) in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6748 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr in
                                          match uu____6748 with
                                          | (uu____6755, repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1 in
                                              let uu____6758 =
                                                let uu____6759 =
                                                  let uu____6776 =
                                                    let uu____6787 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____6804 =
                                                      let uu____6815 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____6815] in
                                                    uu____6787 :: uu____6804 in
                                                  (repr2, uu____6776) in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____6759 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6758
                                                FStar_Range.dummyRange in
                                        let mk_repr a wp =
                                          let uu____6881 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          mk_repr' uu____6881 wp in
                                        let destruct_repr t =
                                          let uu____6896 =
                                            let uu____6897 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____6897.FStar_Syntax_Syntax.n in
                                          match uu____6896 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____6908,
                                               (t1, uu____6910)::(wp,
                                                                  uu____6912)::[])
                                              -> (t1, wp)
                                          | uu____6971 ->
                                              failwith "Unexpected repr type" in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____6986 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr in
                                            FStar_All.pipe_right uu____6986
                                              FStar_Util.must in
                                          let uu____7013 = fresh_a_and_wp () in
                                          match uu____7013 with
                                          | (a, uu____7021) ->
                                              let x_a =
                                                let uu____7027 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7027 in
                                              let res =
                                                let wp =
                                                  let uu____7032 =
                                                    let uu____7033 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp in
                                                    FStar_All.pipe_right
                                                      uu____7033
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____7042 =
                                                    let uu____7043 =
                                                      let uu____7052 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_All.pipe_right
                                                        uu____7052
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____7061 =
                                                      let uu____7072 =
                                                        let uu____7081 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a in
                                                        FStar_All.pipe_right
                                                          uu____7081
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____7072] in
                                                    uu____7043 :: uu____7061 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7032 uu____7042
                                                    FStar_Range.dummyRange in
                                                mk_repr a wp in
                                              let k =
                                                let uu____7117 =
                                                  let uu____7126 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____7133 =
                                                    let uu____7142 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a in
                                                    [uu____7142] in
                                                  uu____7126 :: uu____7133 in
                                                let uu____7167 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res in
                                                FStar_Syntax_Util.arrow
                                                  uu____7117 uu____7167 in
                                              let uu____7170 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k in
                                              (match uu____7170 with
                                               | (k1, uu____7178, uu____7179)
                                                   ->
                                                   let env1 =
                                                     let uu____7183 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7183 in
                                                   check_and_gen'
                                                     "return_repr"
                                                     Prims.int_one env1
                                                     return_repr_ts
                                                     (FStar_Pervasives_Native.Some
                                                        k1)) in
                                        log_combinator "return_repr"
                                          return_repr;
                                        (let bind_repr =
                                           let bind_repr_ts =
                                             let uu____7193 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr in
                                             FStar_All.pipe_right uu____7193
                                               FStar_Util.must in
                                           let r =
                                             let uu____7231 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None in
                                             FStar_All.pipe_right uu____7231
                                               FStar_Syntax_Syntax.fv_to_tm in
                                           let uu____7232 = fresh_a_and_wp () in
                                           match uu____7232 with
                                           | (a, wp_sort_a) ->
                                               let uu____7245 =
                                                 fresh_a_and_wp () in
                                               (match uu____7245 with
                                                | (b, wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7261 =
                                                        let uu____7270 =
                                                          let uu____7277 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7277 in
                                                        [uu____7270] in
                                                      let uu____7290 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7261 uu____7290 in
                                                    let wp_f =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_f"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a in
                                                    let wp_g =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "wp_g"
                                                        FStar_Pervasives_Native.None
                                                        wp_sort_a_b in
                                                    let x_a =
                                                      let uu____7296 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7296 in
                                                    let wp_g_x =
                                                      let uu____7298 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g in
                                                      let uu____7299 =
                                                        let uu____7300 =
                                                          let uu____7309 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____7309
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____7300] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7298 uu____7299
                                                        FStar_Range.dummyRange in
                                                    let res =
                                                      let wp =
                                                        let uu____7338 =
                                                          let uu____7339 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp in
                                                          FStar_All.pipe_right
                                                            uu____7339
                                                            FStar_Pervasives_Native.snd in
                                                        let uu____7348 =
                                                          let uu____7349 =
                                                            let uu____7352 =
                                                              let uu____7355
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a in
                                                              let uu____7356
                                                                =
                                                                let uu____7359
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                let uu____7360
                                                                  =
                                                                  let uu____7363
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  let uu____7364
                                                                    =
                                                                    let uu____7367
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____7367] in
                                                                  uu____7363
                                                                    ::
                                                                    uu____7364 in
                                                                uu____7359 ::
                                                                  uu____7360 in
                                                              uu____7355 ::
                                                                uu____7356 in
                                                            r :: uu____7352 in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7349 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7338
                                                          uu____7348
                                                          FStar_Range.dummyRange in
                                                      mk_repr b wp in
                                                    let maybe_range_arg =
                                                      let uu____7385 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs in
                                                      if uu____7385
                                                      then
                                                        let uu____7394 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range in
                                                        let uu____7401 =
                                                          let uu____7410 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          [uu____7410] in
                                                        uu____7394 ::
                                                          uu____7401
                                                      else [] in
                                                    let k =
                                                      let uu____7445 =
                                                        let uu____7454 =
                                                          let uu____7463 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a in
                                                          let uu____7470 =
                                                            let uu____7479 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b in
                                                            [uu____7479] in
                                                          uu____7463 ::
                                                            uu____7470 in
                                                        let uu____7504 =
                                                          let uu____7513 =
                                                            let uu____7522 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f in
                                                            let uu____7529 =
                                                              let uu____7538
                                                                =
                                                                let uu____7545
                                                                  =
                                                                  let uu____7546
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  mk_repr a
                                                                    uu____7546 in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7545 in
                                                              let uu____7547
                                                                =
                                                                let uu____7556
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                let uu____7563
                                                                  =
                                                                  let uu____7572
                                                                    =
                                                                    let uu____7579
                                                                    =
                                                                    let uu____7580
                                                                    =
                                                                    let uu____7589
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____7589] in
                                                                    let uu____7608
                                                                    =
                                                                    let uu____7611
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7611 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7580
                                                                    uu____7608 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7579 in
                                                                  [uu____7572] in
                                                                uu____7556 ::
                                                                  uu____7563 in
                                                              uu____7538 ::
                                                                uu____7547 in
                                                            uu____7522 ::
                                                              uu____7529 in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7513 in
                                                        FStar_List.append
                                                          uu____7454
                                                          uu____7504 in
                                                      let uu____7656 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7445 uu____7656 in
                                                    let uu____7659 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k in
                                                    (match uu____7659 with
                                                     | (k1, uu____7667,
                                                        uu____7668) ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___808_7678
                                                                = env1 in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___808_7678.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____7679
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____7679) in
                                                         check_and_gen'
                                                           "bind_repr"
                                                           (Prims.of_int (2))
                                                           env2 bind_repr_ts
                                                           (FStar_Pervasives_Native.Some
                                                              k1))) in
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
                                              (let uu____7698 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7710 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs in
                                                    match uu____7710 with
                                                    | (usubst, uvs) ->
                                                        let uu____7733 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs in
                                                        let uu____7734 =
                                                          let uu___821_7735 =
                                                            act in
                                                          let uu____7736 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn in
                                                          let uu____7737 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___821_7735.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___821_7735.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___821_7735.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7736;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7737
                                                          } in
                                                        (uu____7733,
                                                          uu____7734)) in
                                               match uu____7698 with
                                               | (env1, act1) ->
                                                   let act_typ =
                                                     let uu____7741 =
                                                       let uu____7742 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                       uu____7742.FStar_Syntax_Syntax.n in
                                                     match uu____7741 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1, c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c in
                                                         let uu____7768 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname in
                                                         if uu____7768
                                                         then
                                                           let uu____7769 =
                                                             let uu____7772 =
                                                               let uu____7773
                                                                 =
                                                                 let uu____7774
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7774 in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7773 in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7772 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7769
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7796 ->
                                                         act1.FStar_Syntax_Syntax.action_typ in
                                                   let uu____7797 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ in
                                                   (match uu____7797 with
                                                    | (act_typ1, uu____7805,
                                                       g_t) ->
                                                        let env' =
                                                          let uu___838_7808 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1 in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___838_7808.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          } in
                                                        ((let uu____7810 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED") in
                                                          if uu____7810
                                                          then
                                                            let uu____7811 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____7812 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            let uu____7813 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1 in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7811
                                                              uu____7812
                                                              uu____7813
                                                          else ());
                                                         (let uu____7815 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn in
                                                          match uu____7815
                                                          with
                                                          | (act_defn,
                                                             uu____7823, g_a)
                                                              ->
                                                              let act_defn1 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                  env1
                                                                  act_defn in
                                                              let act_typ2 =
                                                                FStar_TypeChecker_Normalize.normalize
                                                                  [FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                  FStar_TypeChecker_Env.Eager_unfolding;
                                                                  FStar_TypeChecker_Env.Beta]
                                                                  env1
                                                                  act_typ1 in
                                                              let uu____7827
                                                                =
                                                                let act_typ3
                                                                  =
                                                                  FStar_Syntax_Subst.compress
                                                                    act_typ2 in
                                                                match 
                                                                  act_typ3.FStar_Syntax_Syntax.n
                                                                with
                                                                | FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____7863
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____7863
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____7875)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____7882
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____7882 in
                                                                    let uu____7885
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____7885
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____7899,
                                                                    g) ->
                                                                    (k1, g)))
                                                                | uu____7903
                                                                    ->
                                                                    let uu____7904
                                                                    =
                                                                    let uu____7909
                                                                    =
                                                                    let uu____7910
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____7911
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____7910
                                                                    uu____7911 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____7909) in
                                                                    FStar_Errors.raise_error
                                                                    uu____7904
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                              (match uu____7827
                                                               with
                                                               | (expected_k,
                                                                  g_k) ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                   ((
                                                                    let uu____7926
                                                                    =
                                                                    let uu____7927
                                                                    =
                                                                    let uu____7928
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____7928 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____7927 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____7926);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____7930
                                                                    =
                                                                    let uu____7931
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____7931.FStar_Syntax_Syntax.n in
                                                                    match uu____7930
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____7956
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____7956
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____7963
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____7963
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____7983
                                                                    =
                                                                    let uu____7984
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____7984] in
                                                                    let uu____7985
                                                                    =
                                                                    let uu____7996
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____7996] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____7983;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____7985;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____8021
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8021))
                                                                    | 
                                                                    uu____8024
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____8025
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8045
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8045)) in
                                                                    match uu____8025
                                                                    with
                                                                    | 
                                                                    (univs,
                                                                    act_defn2)
                                                                    ->
                                                                    let act_typ4
                                                                    =
                                                                    FStar_TypeChecker_Normalize.normalize
                                                                    [FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ3 in
                                                                    let act_typ5
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    univs
                                                                    act_typ4 in
                                                                    let uu___888_8064
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___888_8064.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___888_8064.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___888_8064.FStar_Syntax_Syntax.action_params);
                                                                    FStar_Syntax_Syntax.action_defn
                                                                    =
                                                                    act_defn2;
                                                                    FStar_Syntax_Syntax.action_typ
                                                                    =
                                                                    act_typ5
                                                                    }))))))) in
                                            FStar_All.pipe_right
                                              ed2.FStar_Syntax_Syntax.actions
                                              (FStar_List.map check_action) in
                                          ((FStar_Pervasives_Native.Some repr),
                                            (FStar_Pervasives_Native.Some
                                               return_repr),
                                            (FStar_Pervasives_Native.Some
                                               bind_repr), actions))))) in
                                match uu____6576 with
                                | (repr, return_repr, bind_repr, actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs in
                                      let uu____8107 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8107 ts1 in
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
                                      } in
                                    let combinators1 =
                                      FStar_Syntax_Util.apply_wp_eff_combinators
                                        cl combinators in
                                    let combinators2 =
                                      match ed2.FStar_Syntax_Syntax.combinators
                                      with
                                      | FStar_Syntax_Syntax.Primitive_eff
                                          uu____8119 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8120 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8121 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected" in
                                    let ed3 =
                                      let uu___908_8123 = ed2 in
                                      let uu____8124 = cl signature in
                                      let uu____8125 =
                                        FStar_List.map
                                          (fun a ->
                                             let uu___911_8133 = a in
                                             let uu____8134 =
                                               let uu____8135 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn)) in
                                               FStar_All.pipe_right
                                                 uu____8135
                                                 FStar_Pervasives_Native.snd in
                                             let uu____8160 =
                                               let uu____8161 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ)) in
                                               FStar_All.pipe_right
                                                 uu____8161
                                                 FStar_Pervasives_Native.snd in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___911_8133.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___911_8133.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___911_8133.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___911_8133.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8134;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8160
                                             }) actions in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___908_8123.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___908_8123.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___908_8123.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___908_8123.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8124;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8125;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___908_8123.FStar_Syntax_Syntax.eff_attrs)
                                      } in
                                    ((let uu____8187 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED") in
                                      if uu____8187
                                      then
                                        let uu____8188 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8188
                                      else ());
                                     ed3)))))))))))))
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun ed ->
      fun quals ->
        let uu____8209 =
          let uu____8224 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
          if uu____8224 then tc_layered_eff_decl else tc_non_layered_eff_decl in
        uu____8209 env ed quals
let (monad_signature :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.term ->
        (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
          FStar_Syntax_Syntax.syntax))
  =
  fun env ->
    fun m ->
      fun s ->
        let fail uu____8269 =
          let uu____8270 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____8275 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____8270 uu____8275 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____8319)::(wp, uu____8321)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8350 -> fail ())
        | uu____8351 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____8363 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____8363
       then
         let uu____8364 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8364
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____8386 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____8386.FStar_Syntax_Syntax.pos in
       let uu____8399 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____8399 with
       | (us, lift, lift_ty) ->
           ((let uu____8410 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____8410
             then
               let uu____8411 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____8416 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____8411 uu____8416
             else ());
            (let uu____8422 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____8422 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____8437 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____8438 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____8439 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____8437 uu____8438 s uu____8439 in
                   let uu____8440 =
                     let uu____8447 =
                       let uu____8452 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____8452
                         (fun uu____8469 ->
                            match uu____8469 with
                            | (t, u) ->
                                let uu____8480 =
                                  let uu____8481 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____8481
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____8480, u)) in
                     match uu____8447 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____8499 =
                             let uu____8500 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____8500.FStar_Syntax_Syntax.n in
                           match uu____8499 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____8512)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____8539 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____8539 with
                                | (a', uu____8549)::bs1 ->
                                    let uu____8569 =
                                      let uu____8570 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____8570
                                        FStar_Pervasives_Native.fst in
                                    let uu____8635 =
                                      let uu____8648 =
                                        let uu____8651 =
                                          let uu____8652 =
                                            let uu____8659 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____8659) in
                                          FStar_Syntax_Syntax.NT uu____8652 in
                                        [uu____8651] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____8648 in
                                    FStar_All.pipe_right uu____8569
                                      uu____8635)
                           | uu____8674 ->
                               let uu____8675 =
                                 let uu____8680 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____8680) in
                               FStar_Errors.raise_error uu____8675 r in
                         let uu____8689 =
                           let uu____8700 =
                             let uu____8705 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____8712 =
                               let uu____8713 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____8713
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____8705 r sub.FStar_Syntax_Syntax.source
                               u_a uu____8712 in
                           match uu____8700 with
                           | (f_sort, g) ->
                               let uu____8734 =
                                 let uu____8741 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____8741
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____8734, g) in
                         (match uu____8689 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____8807 =
                                let uu____8812 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____8813 =
                                  let uu____8814 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____8814
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____8812 r sub.FStar_Syntax_Syntax.target
                                  u_a uu____8813 in
                              (match uu____8807 with
                               | (repr, g_repr) ->
                                   let uu____8831 =
                                     let uu____8836 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____8837 =
                                       let uu____8838 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____8839 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____8838 uu____8839 in
                                     pure_wp_uvar uu____8836 repr uu____8837
                                       r in
                                   (match uu____8831 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____8849 =
                                            let uu____8850 =
                                              let uu____8851 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____8851] in
                                            let uu____8852 =
                                              let uu____8863 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____8863] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____8850;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____8852;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____8849 in
                                        let uu____8896 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____8899 =
                                          let uu____8900 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____8900 guard_wp in
                                        (uu____8896, uu____8899)))) in
                   match uu____8440 with
                   | (k, g_k) ->
                       ((let uu____8910 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____8910
                         then
                           let uu____8911 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____8911
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____8917 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____8917
                          then
                            let uu____8918 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____8918
                          else ());
                         (let sub1 =
                            let uu___1000_8921 = sub in
                            let uu____8922 =
                              let uu____8925 =
                                let uu____8926 =
                                  let uu____8929 =
                                    FStar_All.pipe_right k
                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env) in
                                  FStar_All.pipe_right uu____8929
                                    (FStar_Syntax_Subst.close_univ_vars us1) in
                                (us1, uu____8926) in
                              FStar_Pervasives_Native.Some uu____8925 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___1000_8921.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___1000_8921.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = uu____8922;
                              FStar_Syntax_Syntax.lift =
                                (FStar_Pervasives_Native.Some (us1, lift))
                            } in
                          (let uu____8941 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc") in
                           if uu____8941
                           then
                             let uu____8942 =
                               FStar_Syntax_Print.sub_eff_to_string sub1 in
                             FStar_Util.print1 "Final sub_effect: %s\n"
                               uu____8942
                           else ());
                          sub1))))))))
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env ->
    fun sub ->
      fun r ->
        let check_and_gen1 env1 t k =
          let uu____8975 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____8975 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____8978 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____8978
        then tc_layered_lift env sub
        else
          (let uu____8980 =
             let uu____8987 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____8987 in
           match uu____8980 with
           | (a, wp_a_src) ->
               let uu____8994 =
                 let uu____9001 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9001 in
               (match uu____8994 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9009 =
                        let uu____9012 =
                          let uu____9013 =
                            let uu____9020 = FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____9020) in
                          FStar_Syntax_Syntax.NT uu____9013 in
                        [uu____9012] in
                      FStar_Syntax_Subst.subst uu____9009 wp_b_tgt in
                    let expected_k =
                      let uu____9028 =
                        let uu____9037 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____9044 =
                          let uu____9053 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____9053] in
                        uu____9037 :: uu____9044 in
                      let uu____9078 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____9028 uu____9078 in
                    let repr_type eff_name a1 wp =
                      (let uu____9100 =
                         let uu____9101 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____9101 in
                       if uu____9100
                       then
                         let uu____9102 =
                           let uu____9107 =
                             let uu____9108 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9108 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9107) in
                         let uu____9109 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____9102 uu____9109
                       else ());
                      (let uu____9111 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____9111 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____9143 =
                               let uu____9144 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____9144
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9143 in
                           let uu____9151 =
                             let uu____9152 =
                               let uu____9169 =
                                 let uu____9180 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____9189 =
                                   let uu____9200 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____9200] in
                                 uu____9180 :: uu____9189 in
                               (repr, uu____9169) in
                             FStar_Syntax_Syntax.Tm_app uu____9152 in
                           let uu____9245 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____9151 uu____9245) in
                    let uu____9246 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____9418 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9427 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____9427 with
                              | (usubst, uvs1) ->
                                  let uu____9450 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____9451 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____9450, uu____9451)
                            else (env, lift_wp) in
                          (match uu____9418 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____9496 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____9496)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____9567 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9580 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____9580 with
                              | (usubst, uvs) ->
                                  let uu____9605 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____9605)
                            else ([], lift) in
                          (match uu____9567 with
                           | (uvs, lift1) ->
                               ((let uu____9640 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____9640
                                 then
                                   let uu____9641 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9641
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____9644 =
                                   let uu____9651 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9651 lift1 in
                                 match uu____9644 with
                                 | (lift2, comp, uu____9676) ->
                                     let uu____9677 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____9677 with
                                      | (uu____9706, lift_wp, lift_elab) ->
                                          let lift_wp1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-wp" env lift_wp in
                                          let lift_elab1 =
                                            FStar_TypeChecker_DMFF.recheck_debug
                                              "lift-elab" env lift_elab in
                                          if
                                            (FStar_List.length uvs) =
                                              Prims.int_zero
                                          then
                                            let uu____9733 =
                                              let uu____9744 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____9744 in
                                            let uu____9761 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____9733, uu____9761)
                                          else
                                            (let uu____9789 =
                                               let uu____9800 =
                                                 let uu____9809 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____9809) in
                                               FStar_Pervasives_Native.Some
                                                 uu____9800 in
                                             let uu____9824 =
                                               let uu____9833 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____9833) in
                                             (uu____9789, uu____9824)))))) in
                    (match uu____9246 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1084_9897 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1084_9897.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1084_9897.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1084_9897.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1084_9897.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1084_9897.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1084_9897.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1084_9897.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1084_9897.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1084_9897.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1084_9897.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1084_9897.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1084_9897.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1084_9897.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1084_9897.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1084_9897.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1084_9897.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1084_9897.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1084_9897.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1084_9897.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1084_9897.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1084_9897.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1084_9897.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1084_9897.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1084_9897.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1084_9897.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1084_9897.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1084_9897.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1084_9897.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1084_9897.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1084_9897.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1084_9897.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1084_9897.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1084_9897.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1084_9897.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1084_9897.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1084_9897.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1084_9897.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1084_9897.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1084_9897.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1084_9897.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1084_9897.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1084_9897.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1084_9897.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1084_9897.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1084_9897.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1084_9897.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____9929 =
                                 let uu____9934 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____9934 with
                                 | (usubst, uvs1) ->
                                     let uu____9957 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____9958 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____9957, uu____9958) in
                               (match uu____9929 with
                                | (env2, lift2) ->
                                    let uu____9963 =
                                      let uu____9970 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____9970 in
                                    (match uu____9963 with
                                     | (a1, wp_a_src1) ->
                                         let wp_a =
                                           FStar_Syntax_Syntax.new_bv
                                             FStar_Pervasives_Native.None
                                             wp_a_src1 in
                                         let a_typ =
                                           FStar_Syntax_Syntax.bv_to_name a1 in
                                         let wp_a_typ =
                                           FStar_Syntax_Syntax.bv_to_name
                                             wp_a in
                                         let repr_f =
                                           repr_type
                                             sub.FStar_Syntax_Syntax.source
                                             a_typ wp_a_typ in
                                         let repr_result =
                                           let lift_wp1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.EraseUniverses;
                                               FStar_TypeChecker_Env.AllowUnboundUniverses]
                                               env2
                                               (FStar_Pervasives_Native.snd
                                                  lift_wp) in
                                           let lift_wp_a =
                                             let uu____9996 =
                                               let uu____9997 =
                                                 let uu____10014 =
                                                   let uu____10025 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____10034 =
                                                     let uu____10045 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____10045] in
                                                   uu____10025 :: uu____10034 in
                                                 (lift_wp1, uu____10014) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____9997 in
                                             let uu____10090 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____9996 uu____10090 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____10094 =
                                             let uu____10103 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____10110 =
                                               let uu____10119 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____10126 =
                                                 let uu____10135 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____10135] in
                                               uu____10119 :: uu____10126 in
                                             uu____10103 :: uu____10110 in
                                           let uu____10166 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____10094 uu____10166 in
                                         let uu____10169 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____10169 with
                                          | (expected_k2, uu____10179,
                                             uu____10180) ->
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
                                                       env2 lift2 expected_k2 in
                                                   let uu____10184 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____10184)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____10192 =
                             let uu____10193 =
                               let uu____10194 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____10194
                                 FStar_List.length in
                             uu____10193 <> Prims.int_one in
                           if uu____10192
                           then
                             let uu____10213 =
                               let uu____10218 =
                                 let uu____10219 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____10220 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____10221 =
                                   let uu____10222 =
                                     let uu____10223 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____10223
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____10222
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10219 uu____10220 uu____10221 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10218) in
                             FStar_Errors.raise_error uu____10213 r
                           else ());
                          (let uu____10244 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10246 =
                                  let uu____10247 =
                                    let uu____10250 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____10250
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____10247
                                    FStar_List.length in
                                uu____10246 <> Prims.int_one) in
                           if uu____10244
                           then
                             let uu____10285 =
                               let uu____10290 =
                                 let uu____10291 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____10292 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____10293 =
                                   let uu____10294 =
                                     let uu____10295 =
                                       let uu____10298 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____10298
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____10295
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____10294
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10291 uu____10292 uu____10293 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10290) in
                             FStar_Errors.raise_error uu____10285 r
                           else ());
                          (let uu___1121_10334 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1121_10334.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1121_10334.FStar_Syntax_Syntax.target);
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
  fun env ->
    fun uu____10364 ->
      fun r ->
        match uu____10364 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____10387 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10411 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____10411 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____10442 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____10442 c in
                     let uu____10451 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____10451, uvs1, tps1, c1)) in
            (match uu____10387 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____10471 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____10471 with
                  | (tps2, c2) ->
                      let uu____10486 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____10486 with
                       | (tps3, env3, us) ->
                           let uu____10504 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____10504 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____10530)::uu____10531 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10550 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____10556 =
                                    let uu____10557 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____10557 in
                                  if uu____10556
                                  then
                                    let uu____10558 =
                                      let uu____10563 =
                                        let uu____10564 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____10565 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10564 uu____10565 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10563) in
                                    FStar_Errors.raise_error uu____10558 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____10569 =
                                    let uu____10570 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10570 in
                                  match uu____10569 with
                                  | (uvs2, t) ->
                                      let uu____10599 =
                                        let uu____10604 =
                                          let uu____10617 =
                                            let uu____10618 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____10618.FStar_Syntax_Syntax.n in
                                          (tps4, uu____10617) in
                                        match uu____10604 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____10633, c5)) -> ([], c5)
                                        | (uu____10675,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____10714 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____10599 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____10742 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____10742 with
                                               | (uu____10747, t1) ->
                                                   let uu____10749 =
                                                     let uu____10754 =
                                                       let uu____10755 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____10756 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____10757 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____10755
                                                         uu____10756
                                                         uu____10757 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____10754) in
                                                   FStar_Errors.raise_error
                                                     uu____10749 r)
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
  fun env ->
    fun m ->
      fun n ->
        fun p ->
          fun ts ->
            let eff_name =
              let uu____10793 =
                let uu____10794 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____10794 FStar_Ident.string_of_id in
              let uu____10795 =
                let uu____10796 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____10796 FStar_Ident.string_of_id in
              let uu____10797 =
                let uu____10798 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____10798 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____10793 uu____10795
                uu____10797 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____10804 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____10804 with
            | (us, t, ty) ->
                let uu____10818 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____10818 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____10831 =
                         let uu____10836 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____10836
                           (fun uu____10853 ->
                              match uu____10853 with
                              | (t1, u) ->
                                  let uu____10864 =
                                    let uu____10865 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____10865
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____10864, u)) in
                       match uu____10831 with
                       | (a, u_a) ->
                           let uu____10872 =
                             let uu____10877 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____10877
                               (fun uu____10894 ->
                                  match uu____10894 with
                                  | (t1, u) ->
                                      let uu____10905 =
                                        let uu____10906 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____10906
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____10905, u)) in
                           (match uu____10872 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____10922 =
                                    let uu____10923 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____10923.FStar_Syntax_Syntax.n in
                                  match uu____10922 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____10935) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____10962 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____10962 with
                                       | (a', uu____10972)::(b', uu____10974)::bs1
                                           ->
                                           let uu____11004 =
                                             let uu____11005 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____11005
                                               FStar_Pervasives_Native.fst in
                                           let uu____11070 =
                                             let uu____11083 =
                                               let uu____11086 =
                                                 let uu____11087 =
                                                   let uu____11094 =
                                                     let uu____11097 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____11097
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____11094) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11087 in
                                               let uu____11110 =
                                                 let uu____11113 =
                                                   let uu____11114 =
                                                     let uu____11121 =
                                                       let uu____11124 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____11124
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____11121) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11114 in
                                                 [uu____11113] in
                                               uu____11086 :: uu____11110 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11083 in
                                           FStar_All.pipe_right uu____11004
                                             uu____11070)
                                  | uu____11145 ->
                                      let uu____11146 =
                                        let uu____11151 =
                                          let uu____11152 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____11153 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11152 uu____11153 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11151) in
                                      FStar_Errors.raise_error uu____11146 r in
                                let bs = a :: b :: rest_bs in
                                let uu____11183 =
                                  let uu____11194 =
                                    let uu____11199 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____11200 =
                                      let uu____11201 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____11201
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11199 r m u_a uu____11200 in
                                  match uu____11194 with
                                  | (repr, g) ->
                                      let uu____11222 =
                                        let uu____11229 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____11229
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____11222, g) in
                                (match uu____11183 with
                                 | (f, guard_f) ->
                                     let uu____11260 =
                                       let x_a =
                                         let uu____11278 =
                                           let uu____11279 =
                                             let uu____11280 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____11280
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11279 in
                                         FStar_All.pipe_right uu____11278
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____11295 =
                                         let uu____11300 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____11319 =
                                           let uu____11320 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____11320
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11300 r n u_b uu____11319 in
                                       match uu____11295 with
                                       | (repr, g) ->
                                           let uu____11341 =
                                             let uu____11348 =
                                               let uu____11349 =
                                                 let uu____11350 =
                                                   let uu____11353 =
                                                     let uu____11356 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11356 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11353 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11350 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11349 in
                                             FStar_All.pipe_right uu____11348
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____11341, g) in
                                     (match uu____11260 with
                                      | (g, guard_g) ->
                                          let uu____11399 =
                                            let uu____11404 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____11405 =
                                              let uu____11406 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____11406
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11404 r p u_b uu____11405 in
                                          (match uu____11399 with
                                           | (repr, guard_repr) ->
                                               let uu____11421 =
                                                 let uu____11426 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____11427 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____11426
                                                   repr uu____11427 r in
                                               (match uu____11421 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____11437 =
                                                        let uu____11440 =
                                                          let uu____11441 =
                                                            let uu____11442 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____11442] in
                                                          let uu____11443 =
                                                            let uu____11454 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____11454] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____11441;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____11443;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____11440 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____11437 in
                                                    let guard_eq =
                                                      FStar_TypeChecker_Rel.teq
                                                        env1 ty1 k in
                                                    (FStar_List.iter
                                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                                          env1)
                                                       [guard_f;
                                                       guard_g;
                                                       guard_repr;
                                                       g_pure_wp_uvar;
                                                       guard_eq];
                                                     (let uu____11514 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____11514
                                                      then
                                                        let uu____11515 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____11520 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____11515
                                                          uu____11520
                                                      else ());
                                                     (let uu____11527 =
                                                        let uu____11532 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____11532) in
                                                      FStar_Errors.log_issue
                                                        r uu____11527);
                                                     (let uu____11533 =
                                                        let uu____11534 =
                                                          let uu____11537 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1) in
                                                          FStar_All.pipe_right
                                                            uu____11537
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1) in
                                                        (us1, uu____11534) in
                                                      ((us1, t), uu____11533)))))))))))
let (tc_polymonadic_subcomp :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.tscheme ->
          (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.tscheme))
  =
  fun env0 ->
    fun m ->
      fun n ->
        fun ts ->
          let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
          let combinator_name =
            let uu____11582 =
              let uu____11583 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____11583 FStar_Ident.string_of_id in
            let uu____11584 =
              let uu____11585 =
                let uu____11586 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11586 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____11585 in
            Prims.op_Hat uu____11582 uu____11584 in
          let uu____11587 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____11587 with
          | (us, t, ty) ->
              let uu____11601 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____11601 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____11614 =
                       let uu____11619 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____11619
                         (fun uu____11636 ->
                            match uu____11636 with
                            | (t1, u) ->
                                let uu____11647 =
                                  let uu____11648 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____11648
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____11647, u)) in
                     match uu____11614 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____11664 =
                             let uu____11665 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____11665.FStar_Syntax_Syntax.n in
                           match uu____11664 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____11677)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____11704 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____11704 with
                                | (a', uu____11714)::bs1 ->
                                    let uu____11734 =
                                      let uu____11735 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____11735
                                        FStar_Pervasives_Native.fst in
                                    let uu____11832 =
                                      let uu____11845 =
                                        let uu____11848 =
                                          let uu____11849 =
                                            let uu____11856 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11856) in
                                          FStar_Syntax_Syntax.NT uu____11849 in
                                        [uu____11848] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11845 in
                                    FStar_All.pipe_right uu____11734
                                      uu____11832)
                           | uu____11871 ->
                               let uu____11872 =
                                 let uu____11877 =
                                   let uu____11878 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____11879 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____11878 uu____11879 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____11877) in
                               FStar_Errors.raise_error uu____11872 r in
                         let bs = a :: rest_bs in
                         let uu____11903 =
                           let uu____11914 =
                             let uu____11919 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____11920 =
                               let uu____11921 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11921
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11919 r m u uu____11920 in
                           match uu____11914 with
                           | (repr, g) ->
                               let uu____11942 =
                                 let uu____11949 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____11949
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11942, g) in
                         (match uu____11903 with
                          | (f, guard_f) ->
                              let uu____11980 =
                                let uu____11985 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11986 =
                                  let uu____11987 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11987
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11985 r n u uu____11986 in
                              (match uu____11980 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____12002 =
                                     let uu____12007 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____12008 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____12007 ret_t
                                       uu____12008 r in
                                   (match uu____12002 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____12016 =
                                            let uu____12017 =
                                              let uu____12018 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____12018] in
                                            let uu____12019 =
                                              let uu____12030 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____12030] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____12017;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____12019;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____12016 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____12085 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____12085
                                          then
                                            let uu____12086 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____12086
                                          else ());
                                         (let guard_eq =
                                            FStar_TypeChecker_Rel.teq env ty1
                                              k in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env)
                                            [guard_f;
                                            guard_ret_t;
                                            guard_wp;
                                            guard_eq];
                                          (let k1 =
                                             let uu____12093 =
                                               let uu____12094 =
                                                 FStar_All.pipe_right k
                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____12094
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta;
                                                    FStar_TypeChecker_Env.Eager_unfolding]
                                                    env) in
                                             FStar_All.pipe_right uu____12093
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us1) in
                                           (let uu____12098 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____12098
                                            then
                                              let uu____12099 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____12099
                                            else ());
                                           (let uu____12106 =
                                              let uu____12111 =
                                                FStar_Util.format1
                                                  "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                  combinator_name in
                                              (FStar_Errors.Warning_BleedingEdge_Feature,
                                                uu____12111) in
                                            FStar_Errors.log_issue r
                                              uu____12106);
                                           ((us1, t), (us1, k1)))))))))))