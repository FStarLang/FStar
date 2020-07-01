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
          fun uu____58 ->
            match uu____58 with
            | (us, t) ->
                let uu____80 = FStar_Syntax_Subst.open_univ_vars us t in
                (match uu____80 with
                 | (us1, t1) ->
                     let uu____93 =
                       let uu____98 =
                         let uu____105 =
                           FStar_TypeChecker_Env.push_univ_vars env us1 in
                         FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                           uu____105 t1 in
                       match uu____98 with
                       | (t2, lc, g) ->
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (t2, (lc.FStar_TypeChecker_Common.res_typ))) in
                     (match uu____93 with
                      | (t2, ty) ->
                          let uu____122 =
                            FStar_TypeChecker_Util.generalize_universes env
                              t2 in
                          (match uu____122 with
                           | (g_us, t3) ->
                               let ty1 =
                                 FStar_Syntax_Subst.close_univ_vars g_us ty in
                               (if (FStar_List.length g_us) <> n
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n in
                                     let uu____147 =
                                       let uu____149 =
                                         FStar_All.pipe_right g_us
                                           FStar_List.length in
                                       FStar_All.pipe_right uu____149
                                         FStar_Util.string_of_int in
                                     let uu____156 =
                                       FStar_Syntax_Print.tscheme_to_string
                                         (g_us, t3) in
                                     FStar_Util.format5
                                       "Expected %s:%s to be universe-polymorphic in %s universes, but found %s (tscheme: %s)"
                                       eff_name comb uu____145 uu____147
                                       uu____156 in
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
                                               (fun u1 ->
                                                  fun u2 ->
                                                    let uu____173 =
                                                      FStar_Syntax_Syntax.order_univ_name
                                                        u1 u2 in
                                                    uu____173 =
                                                      Prims.int_zero) us1
                                               g_us) in
                                        if uu____166
                                        then ()
                                        else
                                          (let uu____180 =
                                             let uu____186 =
                                               let uu____188 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   us1 in
                                               let uu____190 =
                                                 FStar_Syntax_Print.univ_names_to_string
                                                   g_us in
                                               FStar_Util.format4
                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                 eff_name comb uu____188
                                                 uu____190 in
                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                               uu____186) in
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
  fun env ->
    fun t ->
      fun reason ->
        fun r ->
          let pure_wp_t =
            let pure_wp_ts =
              let uu____229 =
                FStar_TypeChecker_Env.lookup_definition
                  [FStar_TypeChecker_Env.NoDelta] env
                  FStar_Parser_Const.pure_wp_lid in
              FStar_All.pipe_right uu____229 FStar_Util.must in
            let uu____234 = FStar_TypeChecker_Env.inst_tscheme pure_wp_ts in
            match uu____234 with
            | (uu____239, pure_wp_t) ->
                let uu____241 =
                  let uu____242 =
                    FStar_All.pipe_right t FStar_Syntax_Syntax.as_arg in
                  [uu____242] in
                FStar_Syntax_Syntax.mk_Tm_app pure_wp_t uu____241 r in
          let uu____275 =
            FStar_TypeChecker_Util.new_implicit_var reason r env pure_wp_t in
          match uu____275 with
          | (pure_wp_uvar, uu____293, guard_wp) -> (pure_wp_uvar, guard_wp)
let (check_no_subtyping_for_layered_combinator :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option -> unit)
  =
  fun env ->
    fun t ->
      fun k ->
        (let uu____328 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "LayeredEffectsTc") in
         if uu____328
         then
           let uu____333 = FStar_Syntax_Print.term_to_string t in
           let uu____335 =
             match k with
             | FStar_Pervasives_Native.None -> "None"
             | FStar_Pervasives_Native.Some k1 ->
                 FStar_Syntax_Print.term_to_string k1 in
           FStar_Util.print2
             "Checking that %s is well typed with no subtyping (k:%s)\n"
             uu____333 uu____335
         else ());
        (let env1 =
           let uu___54_344 = env in
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
           } in
         match k with
         | FStar_Pervasives_Native.None ->
             let uu____346 = FStar_TypeChecker_TcTerm.tc_trivial_guard env1 t in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____352 =
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
        (let uu____374 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffectsTc") in
         if uu____374
         then
           let uu____379 = FStar_Syntax_Print.eff_decl_to_string false ed in
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
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 Prims.op_Hat uu____407 ")" in
               Prims.op_Hat "Binders are not supported for layered effects ("
                 uu____405 in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____403) in
           let uu____412 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
           FStar_Errors.raise_error uu____397 uu____412)
        else ();
        (let log_combinator s uu____438 =
           match uu____438 with
           | (us, t, ty) ->
               let uu____467 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffectsTc") in
               if uu____467
               then
                 let uu____472 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____474 = FStar_Syntax_Print.tscheme_to_string (us, t) in
                 let uu____480 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty) in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____472 s
                   uu____474 uu____480
               else () in
         let fresh_a_and_u_a a =
           let uu____505 = FStar_Syntax_Util.type_u () in
           FStar_All.pipe_right uu____505
             (fun uu____522 ->
                match uu____522 with
                | (t, u) ->
                    let uu____533 =
                      let uu____534 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t in
                      FStar_All.pipe_right uu____534
                        FStar_Syntax_Syntax.mk_binder in
                    (uu____533, u)) in
         let fresh_x_a x a =
           let uu____548 =
             let uu____549 =
               let uu____550 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst in
               FStar_All.pipe_right uu____550 FStar_Syntax_Syntax.bv_to_name in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____549 in
           FStar_All.pipe_right uu____548 FStar_Syntax_Syntax.mk_binder in
         let check_and_gen1 =
           let uu____584 =
             FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
           check_and_gen env0 uu____584 in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
           let uu____604 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature in
           match uu____604 with
           | (sig_us, sig_t, sig_ty) ->
               let uu____628 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
               (match uu____628 with
                | (us, t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                    let uu____648 = fresh_a_and_u_a "a" in
                    (match uu____648 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____669 =
                             let uu____670 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst in
                             FStar_All.pipe_right uu____670
                               FStar_Syntax_Syntax.bv_to_name in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____669 in
                         let bs = a :: rest_bs in
                         let k =
                           let uu____701 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff in
                           FStar_Syntax_Util.arrow bs uu____701 in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____706 =
                             let uu____709 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env) in
                             FStar_Syntax_Subst.close_univ_vars us uu____709 in
                           (sig_us, uu____706, sig_ty))))) in
         log_combinator "signature" signature;
         (let repr =
            let repr_ts =
              let uu____736 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              FStar_All.pipe_right uu____736 FStar_Util.must in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
            let uu____764 = check_and_gen1 "repr" Prims.int_one repr_ts in
            match uu____764 with
            | (repr_us, repr_t, repr_ty) ->
                let uu____788 =
                  FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                (match uu____788 with
                 | (us, ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                     let uu____808 = fresh_a_and_u_a "a" in
                     (match uu____808 with
                      | (a, u) ->
                          let rest_bs =
                            let signature_ts =
                              let uu____830 = signature in
                              match uu____830 with
                              | (us1, t, uu____845) -> (us1, t) in
                            let uu____862 =
                              let uu____863 =
                                FStar_All.pipe_right a
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____863
                                FStar_Syntax_Syntax.bv_to_name in
                            FStar_TypeChecker_Util.layered_effect_indices_as_binders
                              env r ed.FStar_Syntax_Syntax.mname signature_ts
                              u uu____862 in
                          let bs = a :: rest_bs in
                          let k =
                            let uu____890 =
                              let uu____893 = FStar_Syntax_Util.type_u () in
                              FStar_All.pipe_right uu____893
                                (fun uu____906 ->
                                   match uu____906 with
                                   | (t, u1) ->
                                       let uu____913 =
                                         let uu____916 =
                                           FStar_TypeChecker_Env.new_u_univ
                                             () in
                                         FStar_Pervasives_Native.Some
                                           uu____916 in
                                       FStar_Syntax_Syntax.mk_Total' t
                                         uu____913) in
                            FStar_Syntax_Util.arrow bs uu____890 in
                          let g = FStar_TypeChecker_Rel.teq env ty k in
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let uu____919 =
                              let uu____922 =
                                FStar_All.pipe_right k
                                  (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                     env) in
                              FStar_Syntax_Subst.close_univ_vars us uu____922 in
                            (repr_us, repr_t, uu____919))))) in
          log_combinator "repr" repr;
          (let fresh_repr r env u a_tm =
             let signature_ts =
               let uu____957 = signature in
               match uu____957 with | (us, t, uu____972) -> (us, t) in
             let repr_ts =
               let uu____990 = repr in
               match uu____990 with | (us, t, uu____1005) -> (us, t) in
             FStar_TypeChecker_Util.fresh_effect_repr env r
               ed.FStar_Syntax_Syntax.mname signature_ts
               (FStar_Pervasives_Native.Some repr_ts) u a_tm in
           let not_an_arrow_error comb n t r =
             let uu____1055 =
               let uu____1061 =
                 let uu____1063 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____1065 = FStar_Util.string_of_int n in
                 let uu____1067 = FStar_Syntax_Print.tag_of_term t in
                 let uu____1069 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format5
                   "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                   uu____1063 comb uu____1065 uu____1067 uu____1069 in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____1061) in
             FStar_Errors.raise_error uu____1055 r in
           let return_repr =
             let return_repr_ts =
               let uu____1099 =
                 FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
               FStar_All.pipe_right uu____1099 FStar_Util.must in
             let r =
               (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
             let uu____1127 =
               check_and_gen1 "return_repr" Prims.int_one return_repr_ts in
             match uu____1127 with
             | (ret_us, ret_t, ret_ty) ->
                 let uu____1151 =
                   FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                 (match uu____1151 with
                  | (us, ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                      (check_no_subtyping_for_layered_combinator env ty
                         FStar_Pervasives_Native.None;
                       (let uu____1172 = fresh_a_and_u_a "a" in
                        match uu____1172 with
                        | (a, u_a) ->
                            let x_a = fresh_x_a "x" a in
                            let rest_bs =
                              let uu____1203 =
                                let uu____1204 =
                                  FStar_Syntax_Subst.compress ty in
                                uu____1204.FStar_Syntax_Syntax.n in
                              match uu____1203 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____1216)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____1244 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  (match uu____1244 with
                                   | (a', uu____1254)::(x', uu____1256)::bs1
                                       ->
                                       let uu____1286 =
                                         let uu____1287 =
                                           let uu____1292 =
                                             let uu____1295 =
                                               let uu____1296 =
                                                 let uu____1303 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a) in
                                                 (a', uu____1303) in
                                               FStar_Syntax_Syntax.NT
                                                 uu____1296 in
                                             [uu____1295] in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____1292 in
                                         FStar_All.pipe_right bs1 uu____1287 in
                                       let uu____1310 =
                                         let uu____1323 =
                                           let uu____1326 =
                                             let uu____1327 =
                                               let uu____1334 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      x_a) in
                                               (x', uu____1334) in
                                             FStar_Syntax_Syntax.NT
                                               uu____1327 in
                                           [uu____1326] in
                                         FStar_Syntax_Subst.subst_binders
                                           uu____1323 in
                                       FStar_All.pipe_right uu____1286
                                         uu____1310)
                              | uu____1349 ->
                                  not_an_arrow_error "return"
                                    (Prims.of_int (2)) ty r in
                            let bs = a :: x_a :: rest_bs in
                            let uu____1373 =
                              let uu____1378 =
                                FStar_TypeChecker_Env.push_binders env bs in
                              let uu____1379 =
                                FStar_All.pipe_right
                                  (FStar_Pervasives_Native.fst a)
                                  FStar_Syntax_Syntax.bv_to_name in
                              fresh_repr r uu____1378 u_a uu____1379 in
                            (match uu____1373 with
                             | (repr1, g) ->
                                 let k =
                                   let uu____1399 =
                                     FStar_Syntax_Syntax.mk_Total' repr1
                                       (FStar_Pervasives_Native.Some u_a) in
                                   FStar_Syntax_Util.arrow bs uu____1399 in
                                 let g_eq =
                                   FStar_TypeChecker_Rel.teq env ty k in
                                 ((let uu____1404 =
                                     FStar_TypeChecker_Env.conj_guard g g_eq in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env uu____1404);
                                  (let uu____1405 =
                                     let uu____1408 =
                                       FStar_All.pipe_right k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env) in
                                     FStar_All.pipe_right uu____1408
                                       (FStar_Syntax_Subst.close_univ_vars us) in
                                   (ret_us, ret_t, uu____1405))))))) in
           log_combinator "return_repr" return_repr;
           (let bind_repr =
              let bind_repr_ts =
                let uu____1437 =
                  FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                FStar_All.pipe_right uu____1437 FStar_Util.must in
              let r =
                (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
              let uu____1449 =
                check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
              match uu____1449 with
              | (bind_us, bind_t, bind_ty) ->
                  let uu____1473 =
                    FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                  (match uu____1473 with
                   | (us, ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                       (check_no_subtyping_for_layered_combinator env ty
                          FStar_Pervasives_Native.None;
                        (let uu____1494 = fresh_a_and_u_a "a" in
                         match uu____1494 with
                         | (a, u_a) ->
                             let uu____1514 = fresh_a_and_u_a "b" in
                             (match uu____1514 with
                              | (b, u_b) ->
                                  let rest_bs =
                                    let uu____1543 =
                                      let uu____1544 =
                                        FStar_Syntax_Subst.compress ty in
                                      uu____1544.FStar_Syntax_Syntax.n in
                                    match uu____1543 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____1556) when
                                        (FStar_List.length bs) >=
                                          (Prims.of_int (4))
                                        ->
                                        let uu____1584 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        (match uu____1584 with
                                         | (a', uu____1594)::(b', uu____1596)::bs1
                                             ->
                                             let uu____1626 =
                                               let uu____1627 =
                                                 FStar_All.pipe_right bs1
                                                   (FStar_List.splitAt
                                                      ((FStar_List.length bs1)
                                                         - (Prims.of_int (2)))) in
                                               FStar_All.pipe_right
                                                 uu____1627
                                                 FStar_Pervasives_Native.fst in
                                             let uu____1725 =
                                               let uu____1738 =
                                                 let uu____1741 =
                                                   let uu____1742 =
                                                     let uu____1749 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a) in
                                                     (a', uu____1749) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1742 in
                                                 let uu____1756 =
                                                   let uu____1759 =
                                                     let uu____1760 =
                                                       let uu____1767 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b) in
                                                       (b', uu____1767) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____1760 in
                                                   [uu____1759] in
                                                 uu____1741 :: uu____1756 in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1738 in
                                             FStar_All.pipe_right uu____1626
                                               uu____1725)
                                    | uu____1782 ->
                                        not_an_arrow_error "bind"
                                          (Prims.of_int (4)) ty r in
                                  let bs = a :: b :: rest_bs in
                                  let uu____1806 =
                                    let uu____1817 =
                                      let uu____1822 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____1823 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____1822 u_a uu____1823 in
                                    match uu____1817 with
                                    | (repr1, g) ->
                                        let uu____1838 =
                                          let uu____1845 =
                                            FStar_Syntax_Syntax.gen_bv "f"
                                              FStar_Pervasives_Native.None
                                              repr1 in
                                          FStar_All.pipe_right uu____1845
                                            FStar_Syntax_Syntax.mk_binder in
                                        (uu____1838, g) in
                                  (match uu____1806 with
                                   | (f, guard_f) ->
                                       let uu____1885 =
                                         let x_a = fresh_x_a "x" a in
                                         let uu____1898 =
                                           let uu____1903 =
                                             FStar_TypeChecker_Env.push_binders
                                               env
                                               (FStar_List.append bs [x_a]) in
                                           let uu____1922 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name in
                                           fresh_repr r uu____1903 u_b
                                             uu____1922 in
                                         match uu____1898 with
                                         | (repr1, g) ->
                                             let uu____1937 =
                                               let uu____1944 =
                                                 let uu____1945 =
                                                   let uu____1946 =
                                                     let uu____1949 =
                                                       let uu____1952 =
                                                         FStar_TypeChecker_Env.new_u_univ
                                                           () in
                                                       FStar_Pervasives_Native.Some
                                                         uu____1952 in
                                                     FStar_Syntax_Syntax.mk_Total'
                                                       repr1 uu____1949 in
                                                   FStar_Syntax_Util.arrow
                                                     [x_a] uu____1946 in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "g"
                                                   FStar_Pervasives_Native.None
                                                   uu____1945 in
                                               FStar_All.pipe_right
                                                 uu____1944
                                                 FStar_Syntax_Syntax.mk_binder in
                                             (uu____1937, g) in
                                       (match uu____1885 with
                                        | (g, guard_g) ->
                                            let uu____2004 =
                                              let uu____2009 =
                                                FStar_TypeChecker_Env.push_binders
                                                  env bs in
                                              let uu____2010 =
                                                FStar_All.pipe_right
                                                  (FStar_Pervasives_Native.fst
                                                     b)
                                                  FStar_Syntax_Syntax.bv_to_name in
                                              fresh_repr r uu____2009 u_b
                                                uu____2010 in
                                            (match uu____2004 with
                                             | (repr1, guard_repr) ->
                                                 let uu____2027 =
                                                   let uu____2032 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs in
                                                   let uu____2033 =
                                                     let uu____2035 =
                                                       FStar_Ident.string_of_lid
                                                         ed.FStar_Syntax_Syntax.mname in
                                                     FStar_Util.format1
                                                       "implicit for pure_wp in checking bind for %s"
                                                       uu____2035 in
                                                   pure_wp_uvar uu____2032
                                                     repr1 uu____2033 r in
                                                 (match uu____2027 with
                                                  | (pure_wp_uvar1,
                                                     g_pure_wp_uvar) ->
                                                      let k =
                                                        let uu____2055 =
                                                          let uu____2058 =
                                                            let uu____2059 =
                                                              let uu____2060
                                                                =
                                                                FStar_TypeChecker_Env.new_u_univ
                                                                  () in
                                                              [uu____2060] in
                                                            let uu____2061 =
                                                              let uu____2072
                                                                =
                                                                FStar_All.pipe_right
                                                                  pure_wp_uvar1
                                                                  FStar_Syntax_Syntax.as_arg in
                                                              [uu____2072] in
                                                            {
                                                              FStar_Syntax_Syntax.comp_univs
                                                                = uu____2059;
                                                              FStar_Syntax_Syntax.effect_name
                                                                =
                                                                FStar_Parser_Const.effect_PURE_lid;
                                                              FStar_Syntax_Syntax.result_typ
                                                                = repr1;
                                                              FStar_Syntax_Syntax.effect_args
                                                                = uu____2061;
                                                              FStar_Syntax_Syntax.flags
                                                                = []
                                                            } in
                                                          FStar_Syntax_Syntax.mk_Comp
                                                            uu____2058 in
                                                        FStar_Syntax_Util.arrow
                                                          (FStar_List.append
                                                             bs [f; g])
                                                          uu____2055 in
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
                                                       (let uu____2131 =
                                                          let uu____2134 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env) in
                                                          FStar_All.pipe_right
                                                            uu____2134
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               bind_us) in
                                                        (bind_us, bind_t,
                                                          uu____2131))))))))))) in
            log_combinator "bind_repr" bind_repr;
            (let stronger_repr =
               let stronger_repr =
                 let ts =
                   let uu____2168 =
                     FStar_All.pipe_right ed
                       FStar_Syntax_Util.get_stronger_repr in
                   FStar_All.pipe_right uu____2168 FStar_Util.must in
                 let uu____2179 =
                   let uu____2180 =
                     let uu____2183 =
                       FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____2183
                       FStar_Syntax_Subst.compress in
                   uu____2180.FStar_Syntax_Syntax.n in
                 match uu____2179 with
                 | FStar_Syntax_Syntax.Tm_unknown ->
                     let signature_ts =
                       let uu____2195 = signature in
                       match uu____2195 with | (us, t, uu____2210) -> (us, t) in
                     let uu____2227 =
                       FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                         [FStar_Syntax_Syntax.U_unknown] in
                     (match uu____2227 with
                      | (uu____2236, signature_t) ->
                          let uu____2238 =
                            let uu____2239 =
                              FStar_Syntax_Subst.compress signature_t in
                            uu____2239.FStar_Syntax_Syntax.n in
                          (match uu____2238 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____2247) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               let repr_t =
                                 let repr_ts =
                                   let uu____2273 = repr in
                                   match uu____2273 with
                                   | (us, t, uu____2288) -> (us, t) in
                                 let uu____2305 =
                                   FStar_TypeChecker_Env.inst_tscheme_with
                                     repr_ts [FStar_Syntax_Syntax.U_unknown] in
                                 FStar_All.pipe_right uu____2305
                                   FStar_Pervasives_Native.snd in
                               let repr_t_applied =
                                 let uu____2319 =
                                   let uu____2320 =
                                     let uu____2337 =
                                       let uu____2348 =
                                         let uu____2351 =
                                           FStar_All.pipe_right bs1
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_All.pipe_right uu____2351
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.bv_to_name) in
                                       FStar_All.pipe_right uu____2348
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     (repr_t, uu____2337) in
                                   FStar_Syntax_Syntax.Tm_app uu____2320 in
                                 FStar_Syntax_Syntax.mk uu____2319
                                   FStar_Range.dummyRange in
                               let f_b =
                                 FStar_Syntax_Syntax.null_binder
                                   repr_t_applied in
                               let uu____2401 =
                                 let uu____2402 =
                                   let uu____2405 =
                                     FStar_All.pipe_right f_b
                                       FStar_Pervasives_Native.fst in
                                   FStar_All.pipe_right uu____2405
                                     FStar_Syntax_Syntax.bv_to_name in
                                 FStar_Syntax_Util.abs
                                   (FStar_List.append bs1 [f_b]) uu____2402
                                   FStar_Pervasives_Native.None in
                               ([], uu____2401)
                           | uu____2434 -> failwith "Impossible!"))
                 | uu____2440 -> ts in
               let r =
                 (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
               let uu____2442 =
                 check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
               match uu____2442 with
               | (stronger_us, stronger_t, stronger_ty) ->
                   ((let uu____2467 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                         (FStar_Options.Other "LayeredEffectsTc") in
                     if uu____2467
                     then
                       let uu____2472 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_t) in
                       let uu____2478 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_ty) in
                       FStar_Util.print2
                         "stronger combinator typechecked with term: %s and type: %s\n"
                         uu____2472 uu____2478
                     else ());
                    (let uu____2487 =
                       FStar_Syntax_Subst.open_univ_vars stronger_us
                         stronger_ty in
                     match uu____2487 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2508 = fresh_a_and_u_a "a" in
                           match uu____2508 with
                           | (a, u) ->
                               let rest_bs =
                                 let uu____2537 =
                                   let uu____2538 =
                                     FStar_Syntax_Subst.compress ty in
                                   uu____2538.FStar_Syntax_Syntax.n in
                                 match uu____2537 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs, uu____2550) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____2578 =
                                       FStar_Syntax_Subst.open_binders bs in
                                     (match uu____2578 with
                                      | (a', uu____2588)::bs1 ->
                                          let uu____2608 =
                                            let uu____2609 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one)) in
                                            FStar_All.pipe_right uu____2609
                                              FStar_Pervasives_Native.fst in
                                          let uu____2707 =
                                            let uu____2720 =
                                              let uu____2723 =
                                                let uu____2724 =
                                                  let uu____2731 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a) in
                                                  (a', uu____2731) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____2724 in
                                              [uu____2723] in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____2720 in
                                          FStar_All.pipe_right uu____2608
                                            uu____2707)
                                 | uu____2746 ->
                                     not_an_arrow_error "stronger"
                                       (Prims.of_int (2)) ty r in
                               let bs = a :: rest_bs in
                               let uu____2764 =
                                 let uu____2775 =
                                   let uu____2780 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs in
                                   let uu____2781 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name in
                                   fresh_repr r uu____2780 u uu____2781 in
                                 match uu____2775 with
                                 | (repr1, g) ->
                                     let uu____2796 =
                                       let uu____2803 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1 in
                                       FStar_All.pipe_right uu____2803
                                         FStar_Syntax_Syntax.mk_binder in
                                     (uu____2796, g) in
                               (match uu____2764 with
                                | (f, guard_f) ->
                                    let uu____2843 =
                                      let uu____2848 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____2849 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____2848 u uu____2849 in
                                    (match uu____2843 with
                                     | (ret_t, guard_ret_t) ->
                                         let uu____2866 =
                                           let uu____2871 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs in
                                           let uu____2872 =
                                             let uu____2874 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             FStar_Util.format1
                                               "implicit for pure_wp in checking stronger for %s"
                                               uu____2874 in
                                           pure_wp_uvar uu____2871 ret_t
                                             uu____2872 r in
                                         (match uu____2866 with
                                          | (pure_wp_uvar1, guard_wp) ->
                                              let c =
                                                let uu____2892 =
                                                  let uu____2893 =
                                                    let uu____2894 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        () in
                                                    [uu____2894] in
                                                  let uu____2895 =
                                                    let uu____2906 =
                                                      FStar_All.pipe_right
                                                        pure_wp_uvar1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____2906] in
                                                  {
                                                    FStar_Syntax_Syntax.comp_univs
                                                      = uu____2893;
                                                    FStar_Syntax_Syntax.effect_name
                                                      =
                                                      FStar_Parser_Const.effect_PURE_lid;
                                                    FStar_Syntax_Syntax.result_typ
                                                      = ret_t;
                                                    FStar_Syntax_Syntax.effect_args
                                                      = uu____2895;
                                                    FStar_Syntax_Syntax.flags
                                                      = []
                                                  } in
                                                FStar_Syntax_Syntax.mk_Comp
                                                  uu____2892 in
                                              let k =
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs [f])
                                                  c in
                                              ((let uu____2961 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "LayeredEffectsTc") in
                                                if uu____2961
                                                then
                                                  let uu____2966 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected type of subcomp before unification: %s\n"
                                                    uu____2966
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
                                                (let uu____2973 =
                                                   let uu____2976 =
                                                     let uu____2977 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____2977
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   FStar_All.pipe_right
                                                     uu____2976
                                                     (FStar_Syntax_Subst.close_univ_vars
                                                        stronger_us) in
                                                 (stronger_us, stronger_t,
                                                   uu____2973))))))))))) in
             log_combinator "stronger_repr" stronger_repr;
             (let if_then_else =
                let if_then_else_ts =
                  let ts =
                    let uu____3015 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_layered_if_then_else_combinator in
                    FStar_All.pipe_right uu____3015 FStar_Util.must in
                  let uu____3030 =
                    let uu____3031 =
                      let uu____3034 =
                        FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                      FStar_All.pipe_right uu____3034
                        FStar_Syntax_Subst.compress in
                    uu____3031.FStar_Syntax_Syntax.n in
                  match uu____3030 with
                  | FStar_Syntax_Syntax.Tm_unknown ->
                      let signature_ts =
                        let uu____3054 = signature in
                        match uu____3054 with
                        | (us, t, uu____3069) -> (us, t) in
                      let uu____3086 =
                        FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                          [FStar_Syntax_Syntax.U_unknown] in
                      (match uu____3086 with
                       | (uu____3095, signature_t) ->
                           let uu____3097 =
                             let uu____3098 =
                               FStar_Syntax_Subst.compress signature_t in
                             uu____3098.FStar_Syntax_Syntax.n in
                           (match uu____3097 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3106)
                                ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs in
                                let repr_t =
                                  let repr_ts =
                                    let uu____3132 = repr in
                                    match uu____3132 with
                                    | (us, t, uu____3147) -> (us, t) in
                                  let uu____3164 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      repr_ts [FStar_Syntax_Syntax.U_unknown] in
                                  FStar_All.pipe_right uu____3164
                                    FStar_Pervasives_Native.snd in
                                let repr_t_applied =
                                  let uu____3178 =
                                    let uu____3179 =
                                      let uu____3196 =
                                        let uu____3207 =
                                          let uu____3210 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.map
                                                 FStar_Pervasives_Native.fst) in
                                          FStar_All.pipe_right uu____3210
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.bv_to_name) in
                                        FStar_All.pipe_right uu____3207
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.as_arg) in
                                      (repr_t, uu____3196) in
                                    FStar_Syntax_Syntax.Tm_app uu____3179 in
                                  FStar_Syntax_Syntax.mk uu____3178
                                    FStar_Range.dummyRange in
                                let f_b =
                                  FStar_Syntax_Syntax.null_binder
                                    repr_t_applied in
                                let g_b =
                                  FStar_Syntax_Syntax.null_binder
                                    repr_t_applied in
                                let b_b =
                                  FStar_Syntax_Syntax.null_binder
                                    FStar_Syntax_Util.t_bool in
                                let uu____3262 =
                                  FStar_Syntax_Util.abs
                                    (FStar_List.append bs1 [f_b; g_b; b_b])
                                    repr_t_applied
                                    FStar_Pervasives_Native.None in
                                ([], uu____3262)
                            | uu____3293 -> failwith "Impossible!"))
                  | uu____3299 -> ts in
                let r =
                  (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                let uu____3301 =
                  check_and_gen1 "if_then_else" Prims.int_one if_then_else_ts in
                match uu____3301 with
                | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                    let uu____3325 =
                      FStar_Syntax_Subst.open_univ_vars if_then_else_us
                        if_then_else_t in
                    (match uu____3325 with
                     | (us, t) ->
                         let uu____3344 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_ty in
                         (match uu____3344 with
                          | (uu____3361, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 t (FStar_Pervasives_Native.Some ty);
                               (let uu____3365 = fresh_a_and_u_a "a" in
                                match uu____3365 with
                                | (a, u_a) ->
                                    let rest_bs =
                                      let uu____3394 =
                                        let uu____3395 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____3395.FStar_Syntax_Syntax.n in
                                      match uu____3394 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____3407) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____3435 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____3435 with
                                           | (a', uu____3445)::bs1 ->
                                               let uu____3465 =
                                                 let uu____3466 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____3466
                                                   FStar_Pervasives_Native.fst in
                                               let uu____3564 =
                                                 let uu____3577 =
                                                   let uu____3580 =
                                                     let uu____3581 =
                                                       let uu____3588 =
                                                         let uu____3591 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____3591
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       (a', uu____3588) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3581 in
                                                   [uu____3580] in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____3577 in
                                               FStar_All.pipe_right
                                                 uu____3465 uu____3564)
                                      | uu____3612 ->
                                          not_an_arrow_error "if_then_else"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: rest_bs in
                                    let uu____3630 =
                                      let uu____3641 =
                                        let uu____3646 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____3647 =
                                          let uu____3648 =
                                            FStar_All.pipe_right a
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____3648
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____3646 u_a
                                          uu____3647 in
                                      match uu____3641 with
                                      | (repr1, g) ->
                                          let uu____3669 =
                                            let uu____3676 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____3676
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____3669, g) in
                                    (match uu____3630 with
                                     | (f_bs, guard_f) ->
                                         let uu____3716 =
                                           let uu____3727 =
                                             let uu____3732 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3733 =
                                               let uu____3734 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst in
                                               FStar_All.pipe_right
                                                 uu____3734
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____3732 u_a
                                               uu____3733 in
                                           match uu____3727 with
                                           | (repr1, g) ->
                                               let uu____3755 =
                                                 let uu____3762 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____3762
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____3755, g) in
                                         (match uu____3716 with
                                          | (g_bs, guard_g) ->
                                              let p_b =
                                                let uu____3809 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "p"
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Util.t_bool in
                                                FStar_All.pipe_right
                                                  uu____3809
                                                  FStar_Syntax_Syntax.mk_binder in
                                              let uu____3817 =
                                                let uu____3822 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [p_b]) in
                                                let uu____3841 =
                                                  let uu____3842 =
                                                    FStar_All.pipe_right a
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_All.pipe_right
                                                    uu____3842
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____3822 u_a
                                                  uu____3841 in
                                              (match uu____3817 with
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
                                                    (let uu____3902 =
                                                       let uu____3905 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env) in
                                                       FStar_All.pipe_right
                                                         uu____3905
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            if_then_else_us) in
                                                     (if_then_else_us,
                                                       uu____3902,
                                                       if_then_else_ty)))))))))) in
              log_combinator "if_then_else" if_then_else;
              (let r =
                 let uu____3918 =
                   let uu____3921 =
                     let uu____3930 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_layered_if_then_else_combinator in
                     FStar_All.pipe_right uu____3930 FStar_Util.must in
                   FStar_All.pipe_right uu____3921
                     FStar_Pervasives_Native.snd in
                 uu____3918.FStar_Syntax_Syntax.pos in
               let binder_aq_to_arg_aq aq =
                 match aq with
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                     uu____4005) -> aq
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                     uu____4007) ->
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit false)
                 | uu____4009 -> FStar_Pervasives_Native.None in
               let uu____4012 = if_then_else in
               match uu____4012 with
               | (ite_us, ite_t, uu____4027) ->
                   let uu____4040 =
                     FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                   (match uu____4040 with
                    | (us, ite_t1) ->
                        let uu____4047 =
                          let uu____4064 =
                            let uu____4065 =
                              FStar_Syntax_Subst.compress ite_t1 in
                            uu____4065.FStar_Syntax_Syntax.n in
                          match uu____4064 with
                          | FStar_Syntax_Syntax.Tm_abs
                              (bs, uu____4085, uu____4086) ->
                              let bs1 = FStar_Syntax_Subst.open_binders bs in
                              let uu____4112 =
                                let uu____4125 =
                                  let uu____4130 =
                                    let uu____4133 =
                                      let uu____4142 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                (Prims.of_int (3)))) in
                                      FStar_All.pipe_right uu____4142
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____4133
                                      (FStar_List.map
                                         FStar_Pervasives_Native.fst) in
                                  FStar_All.pipe_right uu____4130
                                    (FStar_List.map
                                       FStar_Syntax_Syntax.bv_to_name) in
                                FStar_All.pipe_right uu____4125
                                  (fun l ->
                                     let uu____4298 = l in
                                     match uu____4298 with
                                     | f::g::p::[] -> (f, g, p)) in
                              (match uu____4112 with
                               | (f, g, p) ->
                                   let uu____4369 =
                                     let uu____4370 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     FStar_TypeChecker_Env.push_binders
                                       uu____4370 bs1 in
                                   let uu____4371 =
                                     let uu____4372 =
                                       FStar_All.pipe_right bs1
                                         (FStar_List.map
                                            (fun uu____4397 ->
                                               match uu____4397 with
                                               | (b, qual) ->
                                                   let uu____4416 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       b in
                                                   (uu____4416,
                                                     (binder_aq_to_arg_aq
                                                        qual)))) in
                                     FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                       uu____4372 r in
                                   (uu____4369, uu____4371, f, g, p))
                          | uu____4425 ->
                              failwith
                                "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                        (match uu____4047 with
                         | (env, ite_t_applied, f_t, g_t, p_t) ->
                             let uu____4460 =
                               let uu____4469 = stronger_repr in
                               match uu____4469 with
                               | (uu____4490, subcomp_t, subcomp_ty) ->
                                   let uu____4505 =
                                     FStar_Syntax_Subst.open_univ_vars us
                                       subcomp_t in
                                   (match uu____4505 with
                                    | (uu____4518, subcomp_t1) ->
                                        let uu____4520 =
                                          let uu____4531 =
                                            FStar_Syntax_Subst.open_univ_vars
                                              us subcomp_ty in
                                          match uu____4531 with
                                          | (uu____4546, subcomp_ty1) ->
                                              let uu____4548 =
                                                let uu____4549 =
                                                  FStar_Syntax_Subst.compress
                                                    subcomp_ty1 in
                                                uu____4549.FStar_Syntax_Syntax.n in
                                              (match uu____4548 with
                                               | FStar_Syntax_Syntax.Tm_arrow
                                                   (bs, uu____4563) ->
                                                   let uu____4584 =
                                                     FStar_All.pipe_right bs
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs)
                                                             - Prims.int_one)) in
                                                   (match uu____4584 with
                                                    | (bs_except_last,
                                                       last_b) ->
                                                        let uu____4690 =
                                                          FStar_All.pipe_right
                                                            bs_except_last
                                                            (FStar_List.map
                                                               FStar_Pervasives_Native.snd) in
                                                        let uu____4717 =
                                                          let uu____4720 =
                                                            FStar_All.pipe_right
                                                              last_b
                                                              FStar_List.hd in
                                                          FStar_All.pipe_right
                                                            uu____4720
                                                            FStar_Pervasives_Native.snd in
                                                        (uu____4690,
                                                          uu____4717))
                                               | uu____4763 ->
                                                   failwith
                                                     "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                        (match uu____4520 with
                                         | (aqs_except_last, last_aq) ->
                                             let uu____4797 =
                                               let uu____4808 =
                                                 FStar_All.pipe_right
                                                   aqs_except_last
                                                   (FStar_List.map
                                                      binder_aq_to_arg_aq) in
                                               let uu____4825 =
                                                 FStar_All.pipe_right last_aq
                                                   binder_aq_to_arg_aq in
                                               (uu____4808, uu____4825) in
                                             (match uu____4797 with
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
                                                  let uu____4937 = aux f_t in
                                                  let uu____4940 = aux g_t in
                                                  (uu____4937, uu____4940)))) in
                             (match uu____4460 with
                              | (subcomp_f, subcomp_g) ->
                                  let uu____4957 =
                                    let aux t =
                                      let uu____4974 =
                                        let uu____4975 =
                                          let uu____5002 =
                                            let uu____5019 =
                                              let uu____5028 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  ite_t_applied in
                                              FStar_Util.Inr uu____5028 in
                                            (uu____5019,
                                              FStar_Pervasives_Native.None) in
                                          (t, uu____5002,
                                            FStar_Pervasives_Native.None) in
                                        FStar_Syntax_Syntax.Tm_ascribed
                                          uu____4975 in
                                      FStar_Syntax_Syntax.mk uu____4974 r in
                                    let uu____5069 = aux subcomp_f in
                                    let uu____5070 = aux subcomp_g in
                                    (uu____5069, uu____5070) in
                                  (match uu____4957 with
                                   | (tm_subcomp_ascribed_f,
                                      tm_subcomp_ascribed_g) ->
                                       ((let uu____5074 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____5074
                                         then
                                           let uu____5079 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_f in
                                           let uu____5081 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_g in
                                           FStar_Util.print2
                                             "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                             uu____5079 uu____5081
                                         else ());
                                        (let uu____5086 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env tm_subcomp_ascribed_f in
                                         match uu____5086 with
                                         | (uu____5093, uu____5094, g_f) ->
                                             let g_f1 =
                                               let uu____5097 =
                                                 let uu____5098 =
                                                   let uu____5099 =
                                                     FStar_All.pipe_right p_t
                                                       FStar_Syntax_Util.b2t in
                                                   FStar_All.pipe_right
                                                     uu____5099
                                                     (fun uu____5102 ->
                                                        FStar_TypeChecker_Common.NonTrivial
                                                          uu____5102) in
                                                 FStar_TypeChecker_Env.guard_of_guard_formula
                                                   uu____5098 in
                                               FStar_TypeChecker_Env.imp_guard
                                                 uu____5097 g_f in
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env g_f1;
                                              (let uu____5104 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env tm_subcomp_ascribed_g in
                                               match uu____5104 with
                                               | (uu____5111, uu____5112,
                                                  g_g) ->
                                                   let g_g1 =
                                                     let not_p =
                                                       let uu____5116 =
                                                         let uu____5117 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             FStar_Parser_Const.not_lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             FStar_Pervasives_Native.None in
                                                         FStar_All.pipe_right
                                                           uu____5117
                                                           FStar_Syntax_Syntax.fv_to_tm in
                                                       let uu____5118 =
                                                         let uu____5119 =
                                                           let uu____5128 =
                                                             FStar_All.pipe_right
                                                               p_t
                                                               FStar_Syntax_Util.b2t in
                                                           FStar_All.pipe_right
                                                             uu____5128
                                                             FStar_Syntax_Syntax.as_arg in
                                                         [uu____5119] in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____5116
                                                         uu____5118 r in
                                                     let uu____5155 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         (FStar_TypeChecker_Common.NonTrivial
                                                            not_p) in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____5155 g_g in
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
                   (let uu____5179 =
                      let uu____5185 =
                        let uu____5187 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____5189 =
                          FStar_Ident.string_of_lid
                            act.FStar_Syntax_Syntax.action_name in
                        let uu____5191 =
                          FStar_Syntax_Print.binders_to_string "; "
                            act.FStar_Syntax_Syntax.action_params in
                        FStar_Util.format3
                          "Action %s:%s has non-empty action params (%s)"
                          uu____5187 uu____5189 uu____5191 in
                      (FStar_Errors.Fatal_MalformedActionDeclaration,
                        uu____5185) in
                    FStar_Errors.raise_error uu____5179 r)
                 else ();
                 (let uu____5198 =
                    let uu____5203 =
                      FStar_Syntax_Subst.univ_var_opening
                        act.FStar_Syntax_Syntax.action_univs in
                    match uu____5203 with
                    | (usubst, us) ->
                        let uu____5226 =
                          FStar_TypeChecker_Env.push_univ_vars env us in
                        let uu____5227 =
                          let uu___502_5228 = act in
                          let uu____5229 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_defn in
                          let uu____5230 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_typ in
                          {
                            FStar_Syntax_Syntax.action_name =
                              (uu___502_5228.FStar_Syntax_Syntax.action_name);
                            FStar_Syntax_Syntax.action_unqualified_name =
                              (uu___502_5228.FStar_Syntax_Syntax.action_unqualified_name);
                            FStar_Syntax_Syntax.action_univs = us;
                            FStar_Syntax_Syntax.action_params =
                              (uu___502_5228.FStar_Syntax_Syntax.action_params);
                            FStar_Syntax_Syntax.action_defn = uu____5229;
                            FStar_Syntax_Syntax.action_typ = uu____5230
                          } in
                        (uu____5226, uu____5227) in
                  match uu____5198 with
                  | (env1, act1) ->
                      let act_typ =
                        let uu____5234 =
                          let uu____5235 =
                            FStar_Syntax_Subst.compress
                              act1.FStar_Syntax_Syntax.action_typ in
                          uu____5235.FStar_Syntax_Syntax.n in
                        match uu____5234 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                            let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                            let uu____5261 =
                              FStar_Ident.lid_equals
                                ct.FStar_Syntax_Syntax.effect_name
                                ed.FStar_Syntax_Syntax.mname in
                            if uu____5261
                            then
                              let repr_ts =
                                let uu____5265 = repr in
                                match uu____5265 with
                                | (us, t, uu____5280) -> (us, t) in
                              let repr1 =
                                let uu____5298 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts ct.FStar_Syntax_Syntax.comp_univs in
                                FStar_All.pipe_right uu____5298
                                  FStar_Pervasives_Native.snd in
                              let repr2 =
                                let uu____5308 =
                                  let uu____5309 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ in
                                  uu____5309 ::
                                    (ct.FStar_Syntax_Syntax.effect_args) in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____5308 r in
                              let c1 =
                                let uu____5327 =
                                  let uu____5330 =
                                    FStar_TypeChecker_Env.new_u_univ () in
                                  FStar_Pervasives_Native.Some uu____5330 in
                                FStar_Syntax_Syntax.mk_Total' repr2
                                  uu____5327 in
                              FStar_Syntax_Util.arrow bs c1
                            else act1.FStar_Syntax_Syntax.action_typ
                        | uu____5333 -> act1.FStar_Syntax_Syntax.action_typ in
                      let uu____5334 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          act_typ in
                      (match uu____5334 with
                       | (act_typ1, uu____5342, g_t) ->
                           let uu____5344 =
                             let uu____5351 =
                               let uu___527_5352 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   act_typ1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___527_5352.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___527_5352.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___527_5352.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___527_5352.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___527_5352.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___527_5352.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___527_5352.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___527_5352.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___527_5352.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___527_5352.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   false;
                                 FStar_TypeChecker_Env.effects =
                                   (uu___527_5352.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___527_5352.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___527_5352.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___527_5352.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___527_5352.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___527_5352.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___527_5352.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___527_5352.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___527_5352.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___527_5352.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___527_5352.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___527_5352.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___527_5352.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___527_5352.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___527_5352.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___527_5352.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___527_5352.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___527_5352.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___527_5352.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___527_5352.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___527_5352.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___527_5352.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___527_5352.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___527_5352.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___527_5352.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___527_5352.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___527_5352.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___527_5352.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___527_5352.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___527_5352.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___527_5352.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___527_5352.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___527_5352.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___527_5352.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___527_5352.FStar_TypeChecker_Env.erasable_types_tab);
                                 FStar_TypeChecker_Env.enable_defer_to_tac =
                                   (uu___527_5352.FStar_TypeChecker_Env.enable_defer_to_tac)
                               } in
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu____5351
                               act1.FStar_Syntax_Syntax.action_defn in
                           (match uu____5344 with
                            | (act_defn, uu____5355, g_d) ->
                                ((let uu____5358 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "LayeredEffectsTc") in
                                  if uu____5358
                                  then
                                    let uu____5363 =
                                      FStar_Syntax_Print.term_to_string
                                        act_defn in
                                    let uu____5365 =
                                      FStar_Syntax_Print.term_to_string
                                        act_typ1 in
                                    FStar_Util.print2
                                      "Typechecked action definition: %s and action type: %s\n"
                                      uu____5363 uu____5365
                                  else ());
                                 (let uu____5370 =
                                    let act_typ2 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        act_typ1 in
                                    let uu____5378 =
                                      let uu____5379 =
                                        FStar_Syntax_Subst.compress act_typ2 in
                                      uu____5379.FStar_Syntax_Syntax.n in
                                    match uu____5378 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____5389) ->
                                        let bs1 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        let env2 =
                                          FStar_TypeChecker_Env.push_binders
                                            env1 bs1 in
                                        let uu____5412 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____5412 with
                                         | (t, u) ->
                                             let reason =
                                               let uu____5427 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____5429 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               FStar_Util.format2
                                                 "implicit for return type of action %s:%s"
                                                 uu____5427 uu____5429 in
                                             let uu____5432 =
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r env2 t in
                                             (match uu____5432 with
                                              | (a_tm, uu____5452, g_tm) ->
                                                  let uu____5466 =
                                                    fresh_repr r env2 u a_tm in
                                                  (match uu____5466 with
                                                   | (repr1, g) ->
                                                       let uu____5479 =
                                                         let uu____5482 =
                                                           let uu____5485 =
                                                             let uu____5488 =
                                                               FStar_TypeChecker_Env.new_u_univ
                                                                 () in
                                                             FStar_All.pipe_right
                                                               uu____5488
                                                               (fun
                                                                  uu____5491
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____5491) in
                                                           FStar_Syntax_Syntax.mk_Total'
                                                             repr1 uu____5485 in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____5482 in
                                                       let uu____5492 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g g_tm in
                                                       (uu____5479,
                                                         uu____5492))))
                                    | uu____5495 ->
                                        let uu____5496 =
                                          let uu____5502 =
                                            let uu____5504 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____5506 =
                                              FStar_Ident.string_of_lid
                                                act1.FStar_Syntax_Syntax.action_name in
                                            let uu____5508 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.format3
                                              "Unexpected non-function type for action %s:%s (%s)"
                                              uu____5504 uu____5506
                                              uu____5508 in
                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                            uu____5502) in
                                        FStar_Errors.raise_error uu____5496 r in
                                  match uu____5370 with
                                  | (k, g_k) ->
                                      ((let uu____5525 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsTc") in
                                        if uu____5525
                                        then
                                          let uu____5530 =
                                            FStar_Syntax_Print.term_to_string
                                              k in
                                          FStar_Util.print1
                                            "Expected action type: %s\n"
                                            uu____5530
                                        else ());
                                       (let g =
                                          FStar_TypeChecker_Rel.teq env1
                                            act_typ1 k in
                                        FStar_List.iter
                                          (FStar_TypeChecker_Rel.force_trivial_guard
                                             env1) [g_t; g_d; g_k; g];
                                        (let uu____5538 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____5538
                                         then
                                           let uu____5543 =
                                             FStar_Syntax_Print.term_to_string
                                               k in
                                           FStar_Util.print1
                                             "Expected action type after unification: %s\n"
                                             uu____5543
                                         else ());
                                        (let act_typ2 =
                                           let err_msg t =
                                             let uu____5556 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             let uu____5558 =
                                               FStar_Ident.string_of_lid
                                                 act1.FStar_Syntax_Syntax.action_name in
                                             let uu____5560 =
                                               FStar_Syntax_Print.term_to_string
                                                 t in
                                             FStar_Util.format3
                                               "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                               uu____5556 uu____5558
                                               uu____5560 in
                                           let repr_args t =
                                             let uu____5581 =
                                               let uu____5582 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____5582.FStar_Syntax_Syntax.n in
                                             match uu____5581 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (head, a::is) ->
                                                 let uu____5634 =
                                                   let uu____5635 =
                                                     FStar_Syntax_Subst.compress
                                                       head in
                                                   uu____5635.FStar_Syntax_Syntax.n in
                                                 (match uu____5634 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      (uu____5644, us) ->
                                                      (us,
                                                        (FStar_Pervasives_Native.fst
                                                           a), is)
                                                  | uu____5654 ->
                                                      let uu____5655 =
                                                        let uu____5661 =
                                                          err_msg t in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5661) in
                                                      FStar_Errors.raise_error
                                                        uu____5655 r)
                                             | uu____5670 ->
                                                 let uu____5671 =
                                                   let uu____5677 = err_msg t in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____5677) in
                                                 FStar_Errors.raise_error
                                                   uu____5671 r in
                                           let k1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 k in
                                           let uu____5687 =
                                             let uu____5688 =
                                               FStar_Syntax_Subst.compress k1 in
                                             uu____5688.FStar_Syntax_Syntax.n in
                                           match uu____5687 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, c) ->
                                               let uu____5713 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs c in
                                               (match uu____5713 with
                                                | (bs1, c1) ->
                                                    let uu____5720 =
                                                      repr_args
                                                        (FStar_Syntax_Util.comp_result
                                                           c1) in
                                                    (match uu____5720 with
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
                                                         let uu____5731 =
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             ct in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____5731))
                                           | uu____5734 ->
                                               let uu____5735 =
                                                 let uu____5741 = err_msg k1 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____5741) in
                                               FStar_Errors.raise_error
                                                 uu____5735 r in
                                         (let uu____5745 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____5745
                                          then
                                            let uu____5750 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.print1
                                              "Action type after injecting it into the monad: %s\n"
                                              uu____5750
                                          else ());
                                         (let act2 =
                                            let uu____5756 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env1 act_defn in
                                            match uu____5756 with
                                            | (us, act_defn1) ->
                                                if
                                                  act1.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then
                                                  let uu___600_5770 = act1 in
                                                  let uu____5771 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      us act_typ2 in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___600_5770.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___600_5770.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      = us;
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___600_5770.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____5771
                                                  }
                                                else
                                                  (let uu____5774 =
                                                     ((FStar_List.length us)
                                                        =
                                                        (FStar_List.length
                                                           act1.FStar_Syntax_Syntax.action_univs))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1 ->
                                                             fun u2 ->
                                                               let uu____5781
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2 in
                                                               uu____5781 =
                                                                 Prims.int_zero)
                                                          us
                                                          act1.FStar_Syntax_Syntax.action_univs) in
                                                   if uu____5774
                                                   then
                                                     let uu___605_5786 = act1 in
                                                     let uu____5787 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                         act_typ2 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___605_5786.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___605_5786.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         =
                                                         (uu___605_5786.FStar_Syntax_Syntax.action_univs);
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___605_5786.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = act_defn1;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5787
                                                     }
                                                   else
                                                     (let uu____5790 =
                                                        let uu____5796 =
                                                          let uu____5798 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname in
                                                          let uu____5800 =
                                                            FStar_Ident.string_of_lid
                                                              act1.FStar_Syntax_Syntax.action_name in
                                                          let uu____5802 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              us in
                                                          let uu____5804 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              act1.FStar_Syntax_Syntax.action_univs in
                                                          FStar_Util.format4
                                                            "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                            uu____5798
                                                            uu____5800
                                                            uu____5802
                                                            uu____5804 in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____5796) in
                                                      FStar_Errors.raise_error
                                                        uu____5790 r)) in
                                          act2))))))))) in
               let tschemes_of uu____5829 =
                 match uu____5829 with | (us, t, ty) -> ((us, t), (us, ty)) in
               let combinators =
                 let uu____5874 =
                   let uu____5875 = tschemes_of repr in
                   let uu____5880 = tschemes_of return_repr in
                   let uu____5885 = tschemes_of bind_repr in
                   let uu____5890 = tschemes_of stronger_repr in
                   let uu____5895 = tschemes_of if_then_else in
                   {
                     FStar_Syntax_Syntax.l_repr = uu____5875;
                     FStar_Syntax_Syntax.l_return = uu____5880;
                     FStar_Syntax_Syntax.l_bind = uu____5885;
                     FStar_Syntax_Syntax.l_subcomp = uu____5890;
                     FStar_Syntax_Syntax.l_if_then_else = uu____5895
                   } in
                 FStar_Syntax_Syntax.Layered_eff uu____5874 in
               let uu___614_5900 = ed in
               let uu____5901 =
                 FStar_List.map (tc_action env0)
                   ed.FStar_Syntax_Syntax.actions in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___614_5900.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___614_5900.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs =
                   (uu___614_5900.FStar_Syntax_Syntax.univs);
                 FStar_Syntax_Syntax.binders =
                   (uu___614_5900.FStar_Syntax_Syntax.binders);
                 FStar_Syntax_Syntax.signature =
                   (let uu____5908 = signature in
                    match uu____5908 with | (us, t, uu____5923) -> (us, t));
                 FStar_Syntax_Syntax.combinators = combinators;
                 FStar_Syntax_Syntax.actions = uu____5901;
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___614_5900.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5961 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED") in
         if uu____5961
         then
           let uu____5966 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5966
         else ());
        (let uu____5972 =
           let uu____5977 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
           match uu____5977 with
           | (ed_univs_subst, ed_univs) ->
               let bs =
                 let uu____6001 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders in
                 FStar_Syntax_Subst.open_binders uu____6001 in
               let uu____6002 =
                 let uu____6009 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____6009 bs in
               (match uu____6002 with
                | (bs1, uu____6015, uu____6016) ->
                    let uu____6017 =
                      let tmp_t =
                        let uu____6027 =
                          let uu____6030 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____6035 ->
                                 FStar_Pervasives_Native.Some uu____6035) in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____6030 in
                        FStar_Syntax_Util.arrow bs1 uu____6027 in
                      let uu____6036 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t in
                      match uu____6036 with
                      | (us, tmp_t1) ->
                          let uu____6053 =
                            let uu____6054 =
                              let uu____6055 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals in
                              FStar_All.pipe_right uu____6055
                                FStar_Pervasives_Native.fst in
                            FStar_All.pipe_right uu____6054
                              FStar_Syntax_Subst.close_binders in
                          (us, uu____6053) in
                    (match uu____6017 with
                     | (us, bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____6092 ->
                              let uu____6095 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1 ->
                                        fun u2 ->
                                          let uu____6102 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2 in
                                          uu____6102 = Prims.int_zero)
                                     ed_univs us) in
                              if uu____6095
                              then (us, bs2)
                              else
                                (let uu____6113 =
                                   let uu____6119 =
                                     let uu____6121 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname in
                                     let uu____6123 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs) in
                                     let uu____6125 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us) in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____6121 uu____6123 uu____6125 in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____6119) in
                                 let uu____6129 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Errors.raise_error uu____6113
                                   uu____6129)))) in
         match uu____5972 with
         | (us, bs) ->
             let ed1 =
               let uu___648_6137 = ed in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___648_6137.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___648_6137.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___648_6137.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___648_6137.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___648_6137.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___648_6137.FStar_Syntax_Syntax.eff_attrs)
               } in
             let uu____6138 = FStar_Syntax_Subst.univ_var_opening us in
             (match uu____6138 with
              | (ed_univs_subst, ed_univs) ->
                  let uu____6157 =
                    let uu____6162 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                    FStar_Syntax_Subst.open_binders' uu____6162 in
                  (match uu____6157 with
                   | (ed_bs, ed_bs_subst) ->
                       let ed2 =
                         let op uu____6183 =
                           match uu____6183 with
                           | (us1, t) ->
                               let t1 =
                                 let uu____6203 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst in
                                 FStar_Syntax_Subst.subst uu____6203 t in
                               let uu____6212 =
                                 let uu____6213 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst in
                                 FStar_Syntax_Subst.subst uu____6213 t1 in
                               (us1, uu____6212) in
                         let uu___662_6218 = ed1 in
                         let uu____6219 =
                           op ed1.FStar_Syntax_Syntax.signature in
                         let uu____6220 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators in
                         let uu____6221 =
                           FStar_List.map
                             (fun a ->
                                let uu___665_6229 = a in
                                let uu____6230 =
                                  let uu____6231 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn)) in
                                  FStar_Pervasives_Native.snd uu____6231 in
                                let uu____6242 =
                                  let uu____6243 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ)) in
                                  FStar_Pervasives_Native.snd uu____6243 in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___665_6229.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___665_6229.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___665_6229.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___665_6229.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____6230;
                                  FStar_Syntax_Syntax.action_typ = uu____6242
                                }) ed1.FStar_Syntax_Syntax.actions in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___662_6218.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___662_6218.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___662_6218.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___662_6218.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____6219;
                           FStar_Syntax_Syntax.combinators = uu____6220;
                           FStar_Syntax_Syntax.actions = uu____6221;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___662_6218.FStar_Syntax_Syntax.eff_attrs)
                         } in
                       ((let uu____6255 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED") in
                         if uu____6255
                         then
                           let uu____6260 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2 in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____6260
                         else ());
                        (let env =
                           let uu____6267 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs in
                           FStar_TypeChecker_Env.push_binders uu____6267
                             ed_bs in
                         let check_and_gen' comb n env_opt uu____6302 k =
                           match uu____6302 with
                           | (us1, t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env in
                               let uu____6322 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t in
                               (match uu____6322 with
                                | (us2, t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____6331 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2 in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____6331 t1 k1
                                      | FStar_Pervasives_Native.None ->
                                          let uu____6332 =
                                            let uu____6339 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____6339 t1 in
                                          (match uu____6332 with
                                           | (t2, uu____6341, g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2)) in
                                    let uu____6344 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2 in
                                    (match uu____6344 with
                                     | (g_us, t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____6360 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname in
                                               let uu____6362 =
                                                 FStar_Util.string_of_int n in
                                               let uu____6364 =
                                                 let uu____6366 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length in
                                                 FStar_All.pipe_right
                                                   uu____6366
                                                   FStar_Util.string_of_int in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____6360 comb uu____6362
                                                 uu____6364 in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____6381 ->
                                               let uu____6382 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____6389 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____6389 =
                                                             Prims.int_zero)
                                                      us2 g_us) in
                                               if uu____6382
                                               then (g_us, t3)
                                               else
                                                 (let uu____6400 =
                                                    let uu____6406 =
                                                      let uu____6408 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____6410 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2) in
                                                      let uu____6412 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us) in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____6408 comb
                                                        uu____6410 uu____6412 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____6406) in
                                                  FStar_Errors.raise_error
                                                    uu____6400
                                                    t3.FStar_Syntax_Syntax.pos))))) in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None in
                         (let uu____6420 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED") in
                          if uu____6420
                          then
                            let uu____6425 =
                              FStar_Syntax_Print.tscheme_to_string signature in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____6425
                          else ());
                         (let fresh_a_and_wp uu____6441 =
                            let fail t =
                              let uu____6454 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t in
                              FStar_Errors.raise_error uu____6454
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                            let uu____6470 =
                              FStar_TypeChecker_Env.inst_tscheme signature in
                            match uu____6470 with
                            | (uu____6481, signature1) ->
                                let uu____6483 =
                                  let uu____6484 =
                                    FStar_Syntax_Subst.compress signature1 in
                                  uu____6484.FStar_Syntax_Syntax.n in
                                (match uu____6483 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1, uu____6494) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1 in
                                     (match bs2 with
                                      | (a, uu____6523)::(wp, uu____6525)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6554 -> fail signature1)
                                 | uu____6555 -> fail signature1) in
                          let log_combinator s ts =
                            let uu____6569 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED") in
                            if uu____6569
                            then
                              let uu____6574 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname in
                              let uu____6576 =
                                FStar_Syntax_Print.tscheme_to_string ts in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____6574 s uu____6576
                            else () in
                          let ret_wp =
                            let uu____6582 = fresh_a_and_wp () in
                            match uu____6582 with
                            | (a, wp_sort) ->
                                let k =
                                  let uu____6598 =
                                    let uu____6607 =
                                      FStar_Syntax_Syntax.mk_binder a in
                                    let uu____6614 =
                                      let uu____6623 =
                                        let uu____6630 =
                                          FStar_Syntax_Syntax.bv_to_name a in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6630 in
                                      [uu____6623] in
                                    uu____6607 :: uu____6614 in
                                  let uu____6649 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                  FStar_Syntax_Util.arrow uu____6598
                                    uu____6649 in
                                let uu____6652 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6652
                                  (FStar_Pervasives_Native.Some k) in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6666 = fresh_a_and_wp () in
                             match uu____6666 with
                             | (a, wp_sort_a) ->
                                 let uu____6679 = fresh_a_and_wp () in
                                 (match uu____6679 with
                                  | (b, wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6695 =
                                          let uu____6704 =
                                            let uu____6711 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6711 in
                                          [uu____6704] in
                                        let uu____6724 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____6695
                                          uu____6724 in
                                      let k =
                                        let uu____6730 =
                                          let uu____6739 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____6746 =
                                            let uu____6755 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____6762 =
                                              let uu____6771 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____6778 =
                                                let uu____6787 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a in
                                                let uu____6794 =
                                                  let uu____6803 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b in
                                                  [uu____6803] in
                                                uu____6787 :: uu____6794 in
                                              uu____6771 :: uu____6778 in
                                            uu____6755 :: uu____6762 in
                                          uu____6739 :: uu____6746 in
                                        let uu____6846 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____6730
                                          uu____6846 in
                                      let uu____6849 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6849
                                        (FStar_Pervasives_Native.Some k)) in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6863 = fresh_a_and_wp () in
                              match uu____6863 with
                              | (a, wp_sort_a) ->
                                  let uu____6876 =
                                    FStar_Syntax_Util.type_u () in
                                  (match uu____6876 with
                                   | (t, uu____6882) ->
                                       let k =
                                         let uu____6886 =
                                           let uu____6895 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____6902 =
                                             let uu____6911 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____6918 =
                                               let uu____6927 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____6927] in
                                             uu____6911 :: uu____6918 in
                                           uu____6895 :: uu____6902 in
                                         let uu____6958 =
                                           FStar_Syntax_Syntax.mk_Total t in
                                         FStar_Syntax_Util.arrow uu____6886
                                           uu____6958 in
                                       let uu____6961 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6961
                                         (FStar_Pervasives_Native.Some k)) in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6975 = fresh_a_and_wp () in
                               match uu____6975 with
                               | (a, wp_sort_a) ->
                                   let p =
                                     let uu____6989 =
                                       let uu____6992 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname in
                                       FStar_Pervasives_Native.Some
                                         uu____6992 in
                                     let uu____6993 =
                                       let uu____6994 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____6994
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.new_bv uu____6989
                                       uu____6993 in
                                   let k =
                                     let uu____7006 =
                                       let uu____7015 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____7022 =
                                         let uu____7031 =
                                           FStar_Syntax_Syntax.mk_binder p in
                                         let uu____7038 =
                                           let uu____7047 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a in
                                           let uu____7054 =
                                             let uu____7063 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             [uu____7063] in
                                           uu____7047 :: uu____7054 in
                                         uu____7031 :: uu____7038 in
                                       uu____7015 :: uu____7022 in
                                     let uu____7100 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a in
                                     FStar_Syntax_Util.arrow uu____7006
                                       uu____7100 in
                                   let uu____7103 =
                                     let uu____7108 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                     FStar_All.pipe_right uu____7108
                                       FStar_Util.must in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____7103
                                     (FStar_Pervasives_Native.Some k) in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____7140 = fresh_a_and_wp () in
                                match uu____7140 with
                                | (a, wp_sort_a) ->
                                    let k =
                                      let uu____7156 =
                                        let uu____7165 =
                                          FStar_Syntax_Syntax.mk_binder a in
                                        let uu____7172 =
                                          let uu____7181 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a in
                                          [uu____7181] in
                                        uu____7165 :: uu____7172 in
                                      let uu____7206 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a in
                                      FStar_Syntax_Util.arrow uu____7156
                                        uu____7206 in
                                    let uu____7209 =
                                      let uu____7214 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator in
                                      FStar_All.pipe_right uu____7214
                                        FStar_Util.must in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____7209
                                      (FStar_Pervasives_Native.Some k) in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____7230 = fresh_a_and_wp () in
                                 match uu____7230 with
                                 | (a, wp_sort_a) ->
                                     let b =
                                       let uu____7244 =
                                         let uu____7247 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____7247 in
                                       let uu____7248 =
                                         let uu____7249 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____7249
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____7244
                                         uu____7248 in
                                     let wp_sort_b_a =
                                       let uu____7261 =
                                         let uu____7270 =
                                           let uu____7277 =
                                             FStar_Syntax_Syntax.bv_to_name b in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____7277 in
                                         [uu____7270] in
                                       let uu____7290 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____7261
                                         uu____7290 in
                                     let k =
                                       let uu____7296 =
                                         let uu____7305 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____7312 =
                                           let uu____7321 =
                                             FStar_Syntax_Syntax.mk_binder b in
                                           let uu____7328 =
                                             let uu____7337 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a in
                                             [uu____7337] in
                                           uu____7321 :: uu____7328 in
                                         uu____7305 :: uu____7312 in
                                       let uu____7368 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____7296
                                         uu____7368 in
                                     let uu____7371 =
                                       let uu____7376 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator in
                                       FStar_All.pipe_right uu____7376
                                         FStar_Util.must in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____7371
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____7392 = fresh_a_and_wp () in
                                  match uu____7392 with
                                  | (a, wp_sort_a) ->
                                      let uu____7405 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____7405 with
                                       | (t, uu____7411) ->
                                           let k =
                                             let uu____7415 =
                                               let uu____7424 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____7431 =
                                                 let uu____7440 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____7440] in
                                               uu____7424 :: uu____7431 in
                                             let uu____7465 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t in
                                             FStar_Syntax_Util.arrow
                                               uu____7415 uu____7465 in
                                           let trivial =
                                             let uu____7469 =
                                               let uu____7474 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator in
                                               FStar_All.pipe_right
                                                 uu____7474 FStar_Util.must in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____7469
                                               (FStar_Pervasives_Native.Some
                                                  k) in
                                           (log_combinator "trivial" trivial;
                                            trivial)) in
                                let uu____7489 =
                                  let uu____7506 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr in
                                  match uu____7506 with
                                  | FStar_Pervasives_Native.None ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____7535 ->
                                      let repr =
                                        let uu____7539 = fresh_a_and_wp () in
                                        match uu____7539 with
                                        | (a, wp_sort_a) ->
                                            let uu____7552 =
                                              FStar_Syntax_Util.type_u () in
                                            (match uu____7552 with
                                             | (t, uu____7558) ->
                                                 let k =
                                                   let uu____7562 =
                                                     let uu____7571 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a in
                                                     let uu____7578 =
                                                       let uu____7587 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       [uu____7587] in
                                                     uu____7571 :: uu____7578 in
                                                   let uu____7612 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7562 uu____7612 in
                                                 let uu____7615 =
                                                   let uu____7620 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr in
                                                   FStar_All.pipe_right
                                                     uu____7620
                                                     FStar_Util.must in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7615
                                                   (FStar_Pervasives_Native.Some
                                                      k)) in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7664 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr in
                                          match uu____7664 with
                                          | (uu____7671, repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1 in
                                              let uu____7674 =
                                                let uu____7675 =
                                                  let uu____7692 =
                                                    let uu____7703 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____7720 =
                                                      let uu____7731 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____7731] in
                                                    uu____7703 :: uu____7720 in
                                                  (repr2, uu____7692) in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____7675 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7674
                                                FStar_Range.dummyRange in
                                        let mk_repr a wp =
                                          let uu____7797 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          mk_repr' uu____7797 wp in
                                        let destruct_repr t =
                                          let uu____7812 =
                                            let uu____7813 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____7813.FStar_Syntax_Syntax.n in
                                          match uu____7812 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7824,
                                               (t1, uu____7826)::(wp,
                                                                  uu____7828)::[])
                                              -> (t1, wp)
                                          | uu____7887 ->
                                              failwith "Unexpected repr type" in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7903 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr in
                                            FStar_All.pipe_right uu____7903
                                              FStar_Util.must in
                                          let uu____7930 = fresh_a_and_wp () in
                                          match uu____7930 with
                                          | (a, uu____7938) ->
                                              let x_a =
                                                let uu____7944 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7944 in
                                              let res =
                                                let wp =
                                                  let uu____7950 =
                                                    let uu____7951 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp in
                                                    FStar_All.pipe_right
                                                      uu____7951
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____7960 =
                                                    let uu____7961 =
                                                      let uu____7970 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_All.pipe_right
                                                        uu____7970
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____7979 =
                                                      let uu____7990 =
                                                        let uu____7999 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a in
                                                        FStar_All.pipe_right
                                                          uu____7999
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____7990] in
                                                    uu____7961 :: uu____7979 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7950 uu____7960
                                                    FStar_Range.dummyRange in
                                                mk_repr a wp in
                                              let k =
                                                let uu____8035 =
                                                  let uu____8044 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____8051 =
                                                    let uu____8060 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a in
                                                    [uu____8060] in
                                                  uu____8044 :: uu____8051 in
                                                let uu____8085 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res in
                                                FStar_Syntax_Util.arrow
                                                  uu____8035 uu____8085 in
                                              let uu____8088 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k in
                                              (match uu____8088 with
                                               | (k1, uu____8096, uu____8097)
                                                   ->
                                                   let env1 =
                                                     let uu____8101 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos in
                                                     FStar_Pervasives_Native.Some
                                                       uu____8101 in
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
                                             let uu____8114 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr in
                                             FStar_All.pipe_right uu____8114
                                               FStar_Util.must in
                                           let r =
                                             let uu____8152 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None in
                                             FStar_All.pipe_right uu____8152
                                               FStar_Syntax_Syntax.fv_to_tm in
                                           let uu____8153 = fresh_a_and_wp () in
                                           match uu____8153 with
                                           | (a, wp_sort_a) ->
                                               let uu____8166 =
                                                 fresh_a_and_wp () in
                                               (match uu____8166 with
                                                | (b, wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____8182 =
                                                        let uu____8191 =
                                                          let uu____8198 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____8198 in
                                                        [uu____8191] in
                                                      let uu____8211 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b in
                                                      FStar_Syntax_Util.arrow
                                                        uu____8182 uu____8211 in
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
                                                      let uu____8219 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____8219 in
                                                    let wp_g_x =
                                                      let uu____8222 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g in
                                                      let uu____8223 =
                                                        let uu____8224 =
                                                          let uu____8233 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____8233
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____8224] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____8222 uu____8223
                                                        FStar_Range.dummyRange in
                                                    let res =
                                                      let wp =
                                                        let uu____8262 =
                                                          let uu____8263 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp in
                                                          FStar_All.pipe_right
                                                            uu____8263
                                                            FStar_Pervasives_Native.snd in
                                                        let uu____8272 =
                                                          let uu____8273 =
                                                            let uu____8276 =
                                                              let uu____8279
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a in
                                                              let uu____8280
                                                                =
                                                                let uu____8283
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                let uu____8284
                                                                  =
                                                                  let uu____8287
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  let uu____8288
                                                                    =
                                                                    let uu____8291
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____8291] in
                                                                  uu____8287
                                                                    ::
                                                                    uu____8288 in
                                                                uu____8283 ::
                                                                  uu____8284 in
                                                              uu____8279 ::
                                                                uu____8280 in
                                                            r :: uu____8276 in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____8273 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____8262
                                                          uu____8272
                                                          FStar_Range.dummyRange in
                                                      mk_repr b wp in
                                                    let maybe_range_arg =
                                                      let uu____8309 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs in
                                                      if uu____8309
                                                      then
                                                        let uu____8320 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range in
                                                        let uu____8327 =
                                                          let uu____8336 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          [uu____8336] in
                                                        uu____8320 ::
                                                          uu____8327
                                                      else [] in
                                                    let k =
                                                      let uu____8372 =
                                                        let uu____8381 =
                                                          let uu____8390 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a in
                                                          let uu____8397 =
                                                            let uu____8406 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b in
                                                            [uu____8406] in
                                                          uu____8390 ::
                                                            uu____8397 in
                                                        let uu____8431 =
                                                          let uu____8440 =
                                                            let uu____8449 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f in
                                                            let uu____8456 =
                                                              let uu____8465
                                                                =
                                                                let uu____8472
                                                                  =
                                                                  let uu____8473
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  mk_repr a
                                                                    uu____8473 in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____8472 in
                                                              let uu____8474
                                                                =
                                                                let uu____8483
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                let uu____8490
                                                                  =
                                                                  let uu____8499
                                                                    =
                                                                    let uu____8506
                                                                    =
                                                                    let uu____8507
                                                                    =
                                                                    let uu____8516
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____8516] in
                                                                    let uu____8535
                                                                    =
                                                                    let uu____8538
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____8538 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____8507
                                                                    uu____8535 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____8506 in
                                                                  [uu____8499] in
                                                                uu____8483 ::
                                                                  uu____8490 in
                                                              uu____8465 ::
                                                                uu____8474 in
                                                            uu____8449 ::
                                                              uu____8456 in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____8440 in
                                                        FStar_List.append
                                                          uu____8381
                                                          uu____8431 in
                                                      let uu____8583 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res in
                                                      FStar_Syntax_Util.arrow
                                                        uu____8372 uu____8583 in
                                                    let uu____8586 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k in
                                                    (match uu____8586 with
                                                     | (k1, uu____8594,
                                                        uu____8595) ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___860_8605
                                                                = env1 in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___860_8605.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____8607
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8607) in
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
                                              (let uu____8634 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8648 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs in
                                                    match uu____8648 with
                                                    | (usubst, uvs) ->
                                                        let uu____8671 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs in
                                                        let uu____8672 =
                                                          let uu___873_8673 =
                                                            act in
                                                          let uu____8674 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn in
                                                          let uu____8675 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___873_8673.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___873_8673.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___873_8673.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8674;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8675
                                                          } in
                                                        (uu____8671,
                                                          uu____8672)) in
                                               match uu____8634 with
                                               | (env1, act1) ->
                                                   let act_typ =
                                                     let uu____8679 =
                                                       let uu____8680 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                       uu____8680.FStar_Syntax_Syntax.n in
                                                     match uu____8679 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1, c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c in
                                                         let uu____8706 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname in
                                                         if uu____8706
                                                         then
                                                           let uu____8709 =
                                                             let uu____8712 =
                                                               let uu____8713
                                                                 =
                                                                 let uu____8714
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8714 in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8713 in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8712 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8709
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8737 ->
                                                         act1.FStar_Syntax_Syntax.action_typ in
                                                   let uu____8738 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ in
                                                   (match uu____8738 with
                                                    | (act_typ1, uu____8746,
                                                       g_t) ->
                                                        let env' =
                                                          let uu___890_8749 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1 in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___890_8749.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          } in
                                                        ((let uu____8752 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED") in
                                                          if uu____8752
                                                          then
                                                            let uu____8756 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____8758 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            let uu____8760 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1 in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8756
                                                              uu____8758
                                                              uu____8760
                                                          else ());
                                                         (let uu____8765 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn in
                                                          match uu____8765
                                                          with
                                                          | (act_defn,
                                                             uu____8773, g_a)
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
                                                              let uu____8777
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
                                                                    let uu____8813
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____8813
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____8825)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____8832
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8832 in
                                                                    let uu____8835
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____8835
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____8849,
                                                                    g) ->
                                                                    (k1, g)))
                                                                | uu____8853
                                                                    ->
                                                                    let uu____8854
                                                                    =
                                                                    let uu____8860
                                                                    =
                                                                    let uu____8862
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____8864
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8862
                                                                    uu____8864 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8860) in
                                                                    FStar_Errors.raise_error
                                                                    uu____8854
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                              (match uu____8777
                                                               with
                                                               | (expected_k,
                                                                  g_k) ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                   ((
                                                                    let uu____8882
                                                                    =
                                                                    let uu____8883
                                                                    =
                                                                    let uu____8884
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8884 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8883 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8882);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8886
                                                                    =
                                                                    let uu____8887
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____8887.FStar_Syntax_Syntax.n in
                                                                    match uu____8886
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____8912
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____8912
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____8919
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____8919
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____8939
                                                                    =
                                                                    let uu____8940
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____8940] in
                                                                    let uu____8941
                                                                    =
                                                                    let uu____8952
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____8952] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8939;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8941;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____8977
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8977))
                                                                    | 
                                                                    uu____8980
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____8982
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____9004
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____9004)) in
                                                                    match uu____8982
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
                                                                    let uu___940_9023
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___940_9023.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___940_9023.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___940_9023.FStar_Syntax_Syntax.action_params);
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
                                match uu____7489 with
                                | (repr, return_repr, bind_repr, actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs in
                                      let uu____9066 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____9066 ts1 in
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
                                          uu____9078 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____9079 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____9080 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected" in
                                    let ed3 =
                                      let uu___960_9083 = ed2 in
                                      let uu____9084 = cl signature in
                                      let uu____9085 =
                                        FStar_List.map
                                          (fun a ->
                                             let uu___963_9093 = a in
                                             let uu____9094 =
                                               let uu____9095 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn)) in
                                               FStar_All.pipe_right
                                                 uu____9095
                                                 FStar_Pervasives_Native.snd in
                                             let uu____9120 =
                                               let uu____9121 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ)) in
                                               FStar_All.pipe_right
                                                 uu____9121
                                                 FStar_Pervasives_Native.snd in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___963_9093.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___963_9093.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___963_9093.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___963_9093.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____9094;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____9120
                                             }) actions in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___960_9083.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___960_9083.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___960_9083.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___960_9083.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____9084;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____9085;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___960_9083.FStar_Syntax_Syntax.eff_attrs)
                                      } in
                                    ((let uu____9147 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED") in
                                      if uu____9147
                                      then
                                        let uu____9152 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____9152
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
        let uu____9178 =
          let uu____9193 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
          if uu____9193 then tc_layered_eff_decl else tc_non_layered_eff_decl in
        uu____9178 env ed quals
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
        let fail uu____9243 =
          let uu____9244 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____9250 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____9244 uu____9250 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____9294)::(wp, uu____9296)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____9325 -> fail ())
        | uu____9326 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____9339 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____9339
       then
         let uu____9344 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____9344
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____9369 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____9369.FStar_Syntax_Syntax.pos in
       let uu____9382 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____9382 with
       | (us, lift, lift_ty) ->
           ((let uu____9396 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____9396
             then
               let uu____9401 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____9407 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____9401 uu____9407
             else ());
            (let uu____9416 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____9416 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____9434 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____9436 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____9438 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____9434 uu____9436 s uu____9438 in
                   let uu____9441 =
                     let uu____9448 =
                       let uu____9453 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____9453
                         (fun uu____9470 ->
                            match uu____9470 with
                            | (t, u) ->
                                let uu____9481 =
                                  let uu____9482 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____9482
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____9481, u)) in
                     match uu____9448 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____9501 =
                             let uu____9502 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____9502.FStar_Syntax_Syntax.n in
                           match uu____9501 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____9514)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____9542 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____9542 with
                                | (a', uu____9552)::bs1 ->
                                    let uu____9572 =
                                      let uu____9573 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____9573
                                        FStar_Pervasives_Native.fst in
                                    let uu____9639 =
                                      let uu____9652 =
                                        let uu____9655 =
                                          let uu____9656 =
                                            let uu____9663 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____9663) in
                                          FStar_Syntax_Syntax.NT uu____9656 in
                                        [uu____9655] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____9652 in
                                    FStar_All.pipe_right uu____9572
                                      uu____9639)
                           | uu____9678 ->
                               let uu____9679 =
                                 let uu____9685 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____9685) in
                               FStar_Errors.raise_error uu____9679 r in
                         let uu____9697 =
                           let uu____9708 =
                             let uu____9713 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____9720 =
                               let uu____9721 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____9721
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____9713 r sub.FStar_Syntax_Syntax.source
                               u_a uu____9720 in
                           match uu____9708 with
                           | (f_sort, g) ->
                               let uu____9742 =
                                 let uu____9749 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____9749
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____9742, g) in
                         (match uu____9697 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____9816 =
                                let uu____9821 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____9822 =
                                  let uu____9823 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____9823
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____9821 r sub.FStar_Syntax_Syntax.target
                                  u_a uu____9822 in
                              (match uu____9816 with
                               | (repr, g_repr) ->
                                   let uu____9840 =
                                     let uu____9845 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____9846 =
                                       let uu____9848 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____9850 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____9848 uu____9850 in
                                     pure_wp_uvar uu____9845 repr uu____9846
                                       r in
                                   (match uu____9840 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____9862 =
                                            let uu____9863 =
                                              let uu____9864 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____9864] in
                                            let uu____9865 =
                                              let uu____9876 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____9876] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____9863;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____9865;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____9862 in
                                        let uu____9909 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____9912 =
                                          let uu____9913 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____9913 guard_wp in
                                        (uu____9909, uu____9912)))) in
                   match uu____9441 with
                   | (k, g_k) ->
                       ((let uu____9923 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____9923
                         then
                           let uu____9928 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____9928
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____9937 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____9937
                          then
                            let uu____9942 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____9942
                          else ());
                         (let sub1 =
                            let uu___1052_9948 = sub in
                            let uu____9949 =
                              let uu____9952 =
                                let uu____9953 =
                                  let uu____9956 =
                                    FStar_All.pipe_right k
                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env) in
                                  FStar_All.pipe_right uu____9956
                                    (FStar_Syntax_Subst.close_univ_vars us1) in
                                (us1, uu____9953) in
                              FStar_Pervasives_Native.Some uu____9952 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___1052_9948.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___1052_9948.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = uu____9949;
                              FStar_Syntax_Syntax.lift =
                                (FStar_Pervasives_Native.Some (us1, lift))
                            } in
                          (let uu____9968 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc") in
                           if uu____9968
                           then
                             let uu____9973 =
                               FStar_Syntax_Print.sub_eff_to_string sub1 in
                             FStar_Util.print1 "Final sub_effect: %s\n"
                               uu____9973
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
          let uu____10010 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____10010 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____10013 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____10013
        then tc_layered_lift env sub
        else
          (let uu____10020 =
             let uu____10027 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____10027 in
           match uu____10020 with
           | (a, wp_a_src) ->
               let uu____10034 =
                 let uu____10041 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____10041 in
               (match uu____10034 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____10049 =
                        let uu____10052 =
                          let uu____10053 =
                            let uu____10060 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____10060) in
                          FStar_Syntax_Syntax.NT uu____10053 in
                        [uu____10052] in
                      FStar_Syntax_Subst.subst uu____10049 wp_b_tgt in
                    let expected_k =
                      let uu____10068 =
                        let uu____10077 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____10084 =
                          let uu____10093 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____10093] in
                        uu____10077 :: uu____10084 in
                      let uu____10118 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____10068 uu____10118 in
                    let repr_type eff_name a1 wp =
                      (let uu____10140 =
                         let uu____10142 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____10142 in
                       if uu____10140
                       then
                         let uu____10145 =
                           let uu____10151 =
                             let uu____10153 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____10153 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____10151) in
                         let uu____10157 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____10145 uu____10157
                       else ());
                      (let uu____10160 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____10160 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____10193 =
                               let uu____10194 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____10194
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____10193 in
                           let uu____10201 =
                             let uu____10202 =
                               let uu____10219 =
                                 let uu____10230 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____10239 =
                                   let uu____10250 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____10250] in
                                 uu____10230 :: uu____10239 in
                               (repr, uu____10219) in
                             FStar_Syntax_Syntax.Tm_app uu____10202 in
                           let uu____10295 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____10201 uu____10295) in
                    let uu____10296 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____10469 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____10480 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____10480 with
                              | (usubst, uvs1) ->
                                  let uu____10503 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____10504 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____10503, uu____10504)
                            else (env, lift_wp) in
                          (match uu____10469 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____10554 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____10554)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____10625 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10640 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____10640 with
                              | (usubst, uvs) ->
                                  let uu____10665 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____10665)
                            else ([], lift) in
                          (match uu____10625 with
                           | (uvs, lift1) ->
                               ((let uu____10701 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____10701
                                 then
                                   let uu____10705 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10705
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____10711 =
                                   let uu____10718 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10718 lift1 in
                                 match uu____10711 with
                                 | (lift2, comp, uu____10743) ->
                                     let uu____10744 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____10744 with
                                      | (uu____10773, lift_wp, lift_elab) ->
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
                                            let uu____10805 =
                                              let uu____10816 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____10816 in
                                            let uu____10833 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____10805, uu____10833)
                                          else
                                            (let uu____10862 =
                                               let uu____10873 =
                                                 let uu____10882 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____10882) in
                                               FStar_Pervasives_Native.Some
                                                 uu____10873 in
                                             let uu____10897 =
                                               let uu____10906 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____10906) in
                                             (uu____10862, uu____10897)))))) in
                    (match uu____10296 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1136_10970 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1136_10970.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1136_10970.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1136_10970.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1136_10970.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1136_10970.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1136_10970.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1136_10970.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1136_10970.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1136_10970.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1136_10970.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1136_10970.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1136_10970.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1136_10970.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1136_10970.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1136_10970.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1136_10970.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1136_10970.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1136_10970.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1136_10970.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1136_10970.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1136_10970.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1136_10970.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1136_10970.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1136_10970.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1136_10970.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1136_10970.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1136_10970.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1136_10970.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1136_10970.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1136_10970.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1136_10970.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1136_10970.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1136_10970.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1136_10970.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1136_10970.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1136_10970.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1136_10970.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1136_10970.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1136_10970.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1136_10970.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1136_10970.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1136_10970.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1136_10970.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1136_10970.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1136_10970.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1136_10970.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____11003 =
                                 let uu____11008 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____11008 with
                                 | (usubst, uvs1) ->
                                     let uu____11031 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____11032 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____11031, uu____11032) in
                               (match uu____11003 with
                                | (env2, lift2) ->
                                    let uu____11037 =
                                      let uu____11044 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____11044 in
                                    (match uu____11037 with
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
                                             let uu____11070 =
                                               let uu____11071 =
                                                 let uu____11088 =
                                                   let uu____11099 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____11108 =
                                                     let uu____11119 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____11119] in
                                                   uu____11099 :: uu____11108 in
                                                 (lift_wp1, uu____11088) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____11071 in
                                             let uu____11164 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____11070 uu____11164 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____11168 =
                                             let uu____11177 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____11184 =
                                               let uu____11193 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____11200 =
                                                 let uu____11209 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____11209] in
                                               uu____11193 :: uu____11200 in
                                             uu____11177 :: uu____11184 in
                                           let uu____11240 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____11168 uu____11240 in
                                         let uu____11243 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____11243 with
                                          | (expected_k2, uu____11253,
                                             uu____11254) ->
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
                                                   let uu____11262 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____11262)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____11270 =
                             let uu____11272 =
                               let uu____11274 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11274
                                 FStar_List.length in
                             uu____11272 <> Prims.int_one in
                           if uu____11270
                           then
                             let uu____11297 =
                               let uu____11303 =
                                 let uu____11305 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____11307 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____11309 =
                                   let uu____11311 =
                                     let uu____11313 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____11313
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____11311
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____11305 uu____11307 uu____11309 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____11303) in
                             FStar_Errors.raise_error uu____11297 r
                           else ());
                          (let uu____11340 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____11343 =
                                  let uu____11345 =
                                    let uu____11348 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____11348
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11345
                                    FStar_List.length in
                                uu____11343 <> Prims.int_one) in
                           if uu____11340
                           then
                             let uu____11387 =
                               let uu____11393 =
                                 let uu____11395 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____11397 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____11399 =
                                   let uu____11401 =
                                     let uu____11403 =
                                       let uu____11406 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____11406
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____11403
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____11401
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____11395 uu____11397 uu____11399 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____11393) in
                             FStar_Errors.raise_error uu____11387 r
                           else ());
                          (let uu___1173_11448 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1173_11448.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1173_11448.FStar_Syntax_Syntax.target);
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
    fun uu____11479 ->
      fun r ->
        match uu____11479 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____11502 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____11530 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____11530 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____11561 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____11561 c in
                     let uu____11570 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____11570, uvs1, tps1, c1)) in
            (match uu____11502 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____11590 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____11590 with
                  | (tps2, c2) ->
                      let uu____11605 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____11605 with
                       | (tps3, env3, us) ->
                           let uu____11623 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____11623 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____11649)::uu____11650 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11669 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____11677 =
                                    let uu____11679 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____11679 in
                                  if uu____11677
                                  then
                                    let uu____11682 =
                                      let uu____11688 =
                                        let uu____11690 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____11692 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11690 uu____11692 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11688) in
                                    FStar_Errors.raise_error uu____11682 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____11700 =
                                    let uu____11701 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11701 in
                                  match uu____11700 with
                                  | (uvs2, t) ->
                                      let uu____11730 =
                                        let uu____11735 =
                                          let uu____11748 =
                                            let uu____11749 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____11749.FStar_Syntax_Syntax.n in
                                          (tps4, uu____11748) in
                                        match uu____11735 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11764, c5)) -> ([], c5)
                                        | (uu____11806,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____11845 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____11730 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11877 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____11877 with
                                               | (uu____11882, t1) ->
                                                   let uu____11884 =
                                                     let uu____11890 =
                                                       let uu____11892 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____11894 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____11898 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11892
                                                         uu____11894
                                                         uu____11898 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11890) in
                                                   FStar_Errors.raise_error
                                                     uu____11884 r)
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
              let uu____11940 =
                let uu____11942 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11942 FStar_Ident.string_of_id in
              let uu____11944 =
                let uu____11946 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11946 FStar_Ident.string_of_id in
              let uu____11948 =
                let uu____11950 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11950 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11940 uu____11944
                uu____11948 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____11958 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____11958 with
            | (us, t, ty) ->
                let uu____11974 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____11974 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11987 =
                         let uu____11992 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____11992
                           (fun uu____12009 ->
                              match uu____12009 with
                              | (t1, u) ->
                                  let uu____12020 =
                                    let uu____12021 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____12021
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____12020, u)) in
                       match uu____11987 with
                       | (a, u_a) ->
                           let uu____12029 =
                             let uu____12034 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____12034
                               (fun uu____12051 ->
                                  match uu____12051 with
                                  | (t1, u) ->
                                      let uu____12062 =
                                        let uu____12063 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____12063
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____12062, u)) in
                           (match uu____12029 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____12080 =
                                    let uu____12081 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____12081.FStar_Syntax_Syntax.n in
                                  match uu____12080 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____12093) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____12121 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____12121 with
                                       | (a', uu____12131)::(b', uu____12133)::bs1
                                           ->
                                           let uu____12163 =
                                             let uu____12164 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____12164
                                               FStar_Pervasives_Native.fst in
                                           let uu____12230 =
                                             let uu____12243 =
                                               let uu____12246 =
                                                 let uu____12247 =
                                                   let uu____12254 =
                                                     let uu____12257 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____12257
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____12254) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____12247 in
                                               let uu____12270 =
                                                 let uu____12273 =
                                                   let uu____12274 =
                                                     let uu____12281 =
                                                       let uu____12284 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____12284
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____12281) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____12274 in
                                                 [uu____12273] in
                                               uu____12246 :: uu____12270 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____12243 in
                                           FStar_All.pipe_right uu____12163
                                             uu____12230)
                                  | uu____12305 ->
                                      let uu____12306 =
                                        let uu____12312 =
                                          let uu____12314 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____12316 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____12314 uu____12316 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____12312) in
                                      FStar_Errors.raise_error uu____12306 r in
                                let bs = a :: b :: rest_bs in
                                let uu____12349 =
                                  let uu____12360 =
                                    let uu____12365 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____12366 =
                                      let uu____12367 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____12367
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____12365 r m u_a uu____12366 in
                                  match uu____12360 with
                                  | (repr, g) ->
                                      let uu____12388 =
                                        let uu____12395 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____12395
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____12388, g) in
                                (match uu____12349 with
                                 | (f, guard_f) ->
                                     let uu____12427 =
                                       let x_a =
                                         let uu____12445 =
                                           let uu____12446 =
                                             let uu____12447 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____12447
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____12446 in
                                         FStar_All.pipe_right uu____12445
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____12463 =
                                         let uu____12468 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____12487 =
                                           let uu____12488 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____12488
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____12468 r n u_b uu____12487 in
                                       match uu____12463 with
                                       | (repr, g) ->
                                           let uu____12509 =
                                             let uu____12516 =
                                               let uu____12517 =
                                                 let uu____12518 =
                                                   let uu____12521 =
                                                     let uu____12524 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____12524 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____12521 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____12518 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____12517 in
                                             FStar_All.pipe_right uu____12516
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____12509, g) in
                                     (match uu____12427 with
                                      | (g, guard_g) ->
                                          let uu____12568 =
                                            let uu____12573 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____12574 =
                                              let uu____12575 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____12575
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12573 r p u_b uu____12574 in
                                          (match uu____12568 with
                                           | (repr, guard_repr) ->
                                               let uu____12590 =
                                                 let uu____12595 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____12596 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____12595
                                                   repr uu____12596 r in
                                               (match uu____12590 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____12608 =
                                                        let uu____12611 =
                                                          let uu____12612 =
                                                            let uu____12613 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____12613] in
                                                          let uu____12614 =
                                                            let uu____12625 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____12625] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12612;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12614;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12611 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12608 in
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
                                                     (let uu____12685 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____12685
                                                      then
                                                        let uu____12689 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____12695 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12689
                                                          uu____12695
                                                      else ());
                                                     (let uu____12705 =
                                                        let uu____12711 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12711) in
                                                      FStar_Errors.log_issue
                                                        r uu____12705);
                                                     (let uu____12715 =
                                                        let uu____12716 =
                                                          let uu____12719 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1) in
                                                          FStar_All.pipe_right
                                                            uu____12719
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1) in
                                                        (us1, uu____12716) in
                                                      ((us1, t), uu____12715)))))))))))
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
            let uu____12766 =
              let uu____12768 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____12768 FStar_Ident.string_of_id in
            let uu____12770 =
              let uu____12772 =
                let uu____12774 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____12774 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____12772 in
            Prims.op_Hat uu____12766 uu____12770 in
          let uu____12777 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____12777 with
          | (us, t, ty) ->
              let uu____12793 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____12793 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____12806 =
                       let uu____12811 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____12811
                         (fun uu____12828 ->
                            match uu____12828 with
                            | (t1, u) ->
                                let uu____12839 =
                                  let uu____12840 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____12840
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____12839, u)) in
                     match uu____12806 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____12857 =
                             let uu____12858 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____12858.FStar_Syntax_Syntax.n in
                           match uu____12857 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____12870)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____12898 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____12898 with
                                | (a', uu____12908)::bs1 ->
                                    let uu____12928 =
                                      let uu____12929 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____12929
                                        FStar_Pervasives_Native.fst in
                                    let uu____13027 =
                                      let uu____13040 =
                                        let uu____13043 =
                                          let uu____13044 =
                                            let uu____13051 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____13051) in
                                          FStar_Syntax_Syntax.NT uu____13044 in
                                        [uu____13043] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____13040 in
                                    FStar_All.pipe_right uu____12928
                                      uu____13027)
                           | uu____13066 ->
                               let uu____13067 =
                                 let uu____13073 =
                                   let uu____13075 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____13077 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____13075 uu____13077 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____13073) in
                               FStar_Errors.raise_error uu____13067 r in
                         let bs = a :: rest_bs in
                         let uu____13104 =
                           let uu____13115 =
                             let uu____13120 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____13121 =
                               let uu____13122 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____13122
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____13120 r m u uu____13121 in
                           match uu____13115 with
                           | (repr, g) ->
                               let uu____13143 =
                                 let uu____13150 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____13150
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____13143, g) in
                         (match uu____13104 with
                          | (f, guard_f) ->
                              let uu____13182 =
                                let uu____13187 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____13188 =
                                  let uu____13189 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____13189
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____13187 r n u uu____13188 in
                              (match uu____13182 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____13204 =
                                     let uu____13209 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____13210 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____13209 ret_t
                                       uu____13210 r in
                                   (match uu____13204 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____13220 =
                                            let uu____13221 =
                                              let uu____13222 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____13222] in
                                            let uu____13223 =
                                              let uu____13234 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____13234] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____13221;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____13223;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____13220 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____13289 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____13289
                                          then
                                            let uu____13294 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____13294
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
                                             let uu____13304 =
                                               let uu____13305 =
                                                 FStar_All.pipe_right k
                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____13305
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta;
                                                    FStar_TypeChecker_Env.Eager_unfolding]
                                                    env) in
                                             FStar_All.pipe_right uu____13304
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us1) in
                                           (let uu____13309 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____13309
                                            then
                                              let uu____13314 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____13314
                                            else ());
                                           (let uu____13324 =
                                              let uu____13330 =
                                                FStar_Util.format1
                                                  "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                  combinator_name in
                                              (FStar_Errors.Warning_BleedingEdge_Feature,
                                                uu____13330) in
                                            FStar_Errors.log_issue r
                                              uu____13324);
                                           ((us1, t), (us1, k1)))))))))))