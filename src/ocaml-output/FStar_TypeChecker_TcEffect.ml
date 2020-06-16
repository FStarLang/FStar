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
              let uu____1465 =
                check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
              match uu____1465 with
              | (bind_us, bind_t, bind_ty) ->
                  let uu____1489 =
                    FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                  (match uu____1489 with
                   | (us, ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                       (check_no_subtyping_for_layered_combinator env ty
                          FStar_Pervasives_Native.None;
                        (let uu____1510 = fresh_a_and_u_a "a" in
                         match uu____1510 with
                         | (a, u_a) ->
                             let uu____1530 = fresh_a_and_u_a "b" in
                             (match uu____1530 with
                              | (b, u_b) ->
                                  let rest_bs =
                                    let uu____1559 =
                                      let uu____1560 =
                                        FStar_Syntax_Subst.compress ty in
                                      uu____1560.FStar_Syntax_Syntax.n in
                                    match uu____1559 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____1572) when
                                        (FStar_List.length bs) >=
                                          (Prims.of_int (4))
                                        ->
                                        let uu____1600 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        (match uu____1600 with
                                         | (a', uu____1610)::(b', uu____1612)::bs1
                                             ->
                                             let uu____1642 =
                                               let uu____1643 =
                                                 FStar_All.pipe_right bs1
                                                   (FStar_List.splitAt
                                                      ((FStar_List.length bs1)
                                                         - (Prims.of_int (2)))) in
                                               FStar_All.pipe_right
                                                 uu____1643
                                                 FStar_Pervasives_Native.fst in
                                             let uu____1709 =
                                               let uu____1722 =
                                                 let uu____1725 =
                                                   let uu____1726 =
                                                     let uu____1733 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a) in
                                                     (a', uu____1733) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1726 in
                                                 let uu____1740 =
                                                   let uu____1743 =
                                                     let uu____1744 =
                                                       let uu____1751 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b) in
                                                       (b', uu____1751) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____1744 in
                                                   [uu____1743] in
                                                 uu____1725 :: uu____1740 in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1722 in
                                             FStar_All.pipe_right uu____1642
                                               uu____1709)
                                    | uu____1766 ->
                                        not_an_arrow_error "bind"
                                          (Prims.of_int (4)) ty r in
                                  let bs = a :: b :: rest_bs in
                                  let uu____1790 =
                                    let uu____1801 =
                                      let uu____1806 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____1807 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____1806 u_a uu____1807 in
                                    match uu____1801 with
                                    | (repr1, g) ->
                                        let uu____1822 =
                                          let uu____1829 =
                                            FStar_Syntax_Syntax.gen_bv "f"
                                              FStar_Pervasives_Native.None
                                              repr1 in
                                          FStar_All.pipe_right uu____1829
                                            FStar_Syntax_Syntax.mk_binder in
                                        (uu____1822, g) in
                                  (match uu____1790 with
                                   | (f, guard_f) ->
                                       let uu____1869 =
                                         let x_a = fresh_x_a "x" a in
                                         let uu____1882 =
                                           let uu____1887 =
                                             FStar_TypeChecker_Env.push_binders
                                               env
                                               (FStar_List.append bs [x_a]) in
                                           let uu____1906 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name in
                                           fresh_repr r uu____1887 u_b
                                             uu____1906 in
                                         match uu____1882 with
                                         | (repr1, g) ->
                                             let uu____1921 =
                                               let uu____1928 =
                                                 let uu____1929 =
                                                   let uu____1930 =
                                                     let uu____1933 =
                                                       let uu____1936 =
                                                         FStar_TypeChecker_Env.new_u_univ
                                                           () in
                                                       FStar_Pervasives_Native.Some
                                                         uu____1936 in
                                                     FStar_Syntax_Syntax.mk_Total'
                                                       repr1 uu____1933 in
                                                   FStar_Syntax_Util.arrow
                                                     [x_a] uu____1930 in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "g"
                                                   FStar_Pervasives_Native.None
                                                   uu____1929 in
                                               FStar_All.pipe_right
                                                 uu____1928
                                                 FStar_Syntax_Syntax.mk_binder in
                                             (uu____1921, g) in
                                       (match uu____1869 with
                                        | (g, guard_g) ->
                                            let uu____1988 =
                                              let uu____1993 =
                                                FStar_TypeChecker_Env.push_binders
                                                  env bs in
                                              let uu____1994 =
                                                FStar_All.pipe_right
                                                  (FStar_Pervasives_Native.fst
                                                     b)
                                                  FStar_Syntax_Syntax.bv_to_name in
                                              fresh_repr r uu____1993 u_b
                                                uu____1994 in
                                            (match uu____1988 with
                                             | (repr1, guard_repr) ->
                                                 let uu____2011 =
                                                   let uu____2016 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs in
                                                   let uu____2017 =
                                                     let uu____2019 =
                                                       FStar_Ident.string_of_lid
                                                         ed.FStar_Syntax_Syntax.mname in
                                                     FStar_Util.format1
                                                       "implicit for pure_wp in checking bind for %s"
                                                       uu____2019 in
                                                   pure_wp_uvar uu____2016
                                                     repr1 uu____2017 r in
                                                 (match uu____2011 with
                                                  | (pure_wp_uvar1,
                                                     g_pure_wp_uvar) ->
                                                      let k =
                                                        let uu____2039 =
                                                          let uu____2042 =
                                                            let uu____2043 =
                                                              let uu____2044
                                                                =
                                                                FStar_TypeChecker_Env.new_u_univ
                                                                  () in
                                                              [uu____2044] in
                                                            let uu____2045 =
                                                              let uu____2056
                                                                =
                                                                FStar_All.pipe_right
                                                                  pure_wp_uvar1
                                                                  FStar_Syntax_Syntax.as_arg in
                                                              [uu____2056] in
                                                            {
                                                              FStar_Syntax_Syntax.comp_univs
                                                                = uu____2043;
                                                              FStar_Syntax_Syntax.effect_name
                                                                =
                                                                FStar_Parser_Const.effect_PURE_lid;
                                                              FStar_Syntax_Syntax.result_typ
                                                                = repr1;
                                                              FStar_Syntax_Syntax.effect_args
                                                                = uu____2045;
                                                              FStar_Syntax_Syntax.flags
                                                                = []
                                                            } in
                                                          FStar_Syntax_Syntax.mk_Comp
                                                            uu____2042 in
                                                        FStar_Syntax_Util.arrow
                                                          (FStar_List.append
                                                             bs [f; g])
                                                          uu____2039 in
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
                                                       (let uu____2115 =
                                                          let uu____2118 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env) in
                                                          FStar_All.pipe_right
                                                            uu____2118
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               bind_us) in
                                                        (bind_us, bind_t,
                                                          uu____2115))))))))))) in
            log_combinator "bind_repr" bind_repr;
            (let stronger_repr =
               let stronger_repr =
                 let uu____2147 =
                   FStar_All.pipe_right ed
                     FStar_Syntax_Util.get_stronger_repr in
                 FStar_All.pipe_right uu____2147 FStar_Util.must in
               let r =
                 (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
               let uu____2175 =
                 check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
               match uu____2175 with
               | (stronger_us, stronger_t, stronger_ty) ->
                   ((let uu____2200 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                         (FStar_Options.Other "LayeredEffectsTc") in
                     if uu____2200
                     then
                       let uu____2205 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_t) in
                       let uu____2211 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_ty) in
                       FStar_Util.print2
                         "stronger combinator typechecked with term: %s and type: %s\n"
                         uu____2205 uu____2211
                     else ());
                    (let uu____2220 =
                       FStar_Syntax_Subst.open_univ_vars stronger_us
                         stronger_ty in
                     match uu____2220 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2241 = fresh_a_and_u_a "a" in
                           match uu____2241 with
                           | (a, u) ->
                               let rest_bs =
                                 let uu____2270 =
                                   let uu____2271 =
                                     FStar_Syntax_Subst.compress ty in
                                   uu____2271.FStar_Syntax_Syntax.n in
                                 match uu____2270 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs, uu____2283) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____2311 =
                                       FStar_Syntax_Subst.open_binders bs in
                                     (match uu____2311 with
                                      | (a', uu____2321)::bs1 ->
                                          let uu____2341 =
                                            let uu____2342 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one)) in
                                            FStar_All.pipe_right uu____2342
                                              FStar_Pervasives_Native.fst in
                                          let uu____2440 =
                                            let uu____2453 =
                                              let uu____2456 =
                                                let uu____2457 =
                                                  let uu____2464 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a) in
                                                  (a', uu____2464) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____2457 in
                                              [uu____2456] in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____2453 in
                                          FStar_All.pipe_right uu____2341
                                            uu____2440)
                                 | uu____2479 ->
                                     not_an_arrow_error "stronger"
                                       (Prims.of_int (2)) ty r in
                               let bs = a :: rest_bs in
                               let uu____2497 =
                                 let uu____2508 =
                                   let uu____2513 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs in
                                   let uu____2514 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name in
                                   fresh_repr r uu____2513 u uu____2514 in
                                 match uu____2508 with
                                 | (repr1, g) ->
                                     let uu____2529 =
                                       let uu____2536 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1 in
                                       FStar_All.pipe_right uu____2536
                                         FStar_Syntax_Syntax.mk_binder in
                                     (uu____2529, g) in
                               (match uu____2497 with
                                | (f, guard_f) ->
                                    let uu____2576 =
                                      let uu____2581 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____2582 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____2581 u uu____2582 in
                                    (match uu____2576 with
                                     | (ret_t, guard_ret_t) ->
                                         let uu____2599 =
                                           let uu____2604 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs in
                                           let uu____2605 =
                                             let uu____2607 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             FStar_Util.format1
                                               "implicit for pure_wp in checking stronger for %s"
                                               uu____2607 in
                                           pure_wp_uvar uu____2604 ret_t
                                             uu____2605 r in
                                         (match uu____2599 with
                                          | (pure_wp_uvar1, guard_wp) ->
                                              let c =
                                                let uu____2625 =
                                                  let uu____2626 =
                                                    let uu____2627 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        () in
                                                    [uu____2627] in
                                                  let uu____2628 =
                                                    let uu____2639 =
                                                      FStar_All.pipe_right
                                                        pure_wp_uvar1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____2639] in
                                                  {
                                                    FStar_Syntax_Syntax.comp_univs
                                                      = uu____2626;
                                                    FStar_Syntax_Syntax.effect_name
                                                      =
                                                      FStar_Parser_Const.effect_PURE_lid;
                                                    FStar_Syntax_Syntax.result_typ
                                                      = ret_t;
                                                    FStar_Syntax_Syntax.effect_args
                                                      = uu____2628;
                                                    FStar_Syntax_Syntax.flags
                                                      = []
                                                  } in
                                                FStar_Syntax_Syntax.mk_Comp
                                                  uu____2625 in
                                              let k =
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs [f])
                                                  c in
                                              ((let uu____2694 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "LayeredEffectsTc") in
                                                if uu____2694
                                                then
                                                  let uu____2699 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected type of subcomp before unification: %s\n"
                                                    uu____2699
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
                                                (let uu____2706 =
                                                   let uu____2709 =
                                                     let uu____2710 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____2710
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   FStar_All.pipe_right
                                                     uu____2709
                                                     (FStar_Syntax_Subst.close_univ_vars
                                                        stronger_us) in
                                                 (stronger_us, stronger_t,
                                                   uu____2706))))))))))) in
             log_combinator "stronger_repr" stronger_repr;
             (let if_then_else =
                let if_then_else_ts =
                  let uu____2741 =
                    FStar_All.pipe_right ed
                      FStar_Syntax_Util.get_layered_if_then_else_combinator in
                  FStar_All.pipe_right uu____2741 FStar_Util.must in
                let r =
                  (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                let uu____2781 =
                  check_and_gen1 "if_then_else" Prims.int_one if_then_else_ts in
                match uu____2781 with
                | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                    let uu____2805 =
                      FStar_Syntax_Subst.open_univ_vars if_then_else_us
                        if_then_else_t in
                    (match uu____2805 with
                     | (us, t) ->
                         let uu____2824 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_ty in
                         (match uu____2824 with
                          | (uu____2841, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 t (FStar_Pervasives_Native.Some ty);
                               (let uu____2845 = fresh_a_and_u_a "a" in
                                match uu____2845 with
                                | (a, u_a) ->
                                    let rest_bs =
                                      let uu____2874 =
                                        let uu____2875 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____2875.FStar_Syntax_Syntax.n in
                                      match uu____2874 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____2887) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____2915 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____2915 with
                                           | (a', uu____2925)::bs1 ->
                                               let uu____2945 =
                                                 let uu____2946 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____2946
                                                   FStar_Pervasives_Native.fst in
                                               let uu____3044 =
                                                 let uu____3057 =
                                                   let uu____3060 =
                                                     let uu____3061 =
                                                       let uu____3068 =
                                                         let uu____3071 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____3071
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       (a', uu____3068) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____3061 in
                                                   [uu____3060] in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____3057 in
                                               FStar_All.pipe_right
                                                 uu____2945 uu____3044)
                                      | uu____3092 ->
                                          not_an_arrow_error "if_then_else"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: rest_bs in
                                    let uu____3110 =
                                      let uu____3121 =
                                        let uu____3126 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____3127 =
                                          let uu____3128 =
                                            FStar_All.pipe_right a
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____3128
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____3126 u_a
                                          uu____3127 in
                                      match uu____3121 with
                                      | (repr1, g) ->
                                          let uu____3149 =
                                            let uu____3156 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____3156
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____3149, g) in
                                    (match uu____3110 with
                                     | (f_bs, guard_f) ->
                                         let uu____3196 =
                                           let uu____3207 =
                                             let uu____3212 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3213 =
                                               let uu____3214 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst in
                                               FStar_All.pipe_right
                                                 uu____3214
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____3212 u_a
                                               uu____3213 in
                                           match uu____3207 with
                                           | (repr1, g) ->
                                               let uu____3235 =
                                                 let uu____3242 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____3242
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____3235, g) in
                                         (match uu____3196 with
                                          | (g_bs, guard_g) ->
                                              let p_b =
                                                let uu____3289 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "p"
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Util.ktype0 in
                                                FStar_All.pipe_right
                                                  uu____3289
                                                  FStar_Syntax_Syntax.mk_binder in
                                              let uu____3297 =
                                                let uu____3302 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [p_b]) in
                                                let uu____3321 =
                                                  let uu____3322 =
                                                    FStar_All.pipe_right a
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_All.pipe_right
                                                    uu____3322
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____3302 u_a
                                                  uu____3321 in
                                              (match uu____3297 with
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
                                                    (let uu____3382 =
                                                       let uu____3385 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env) in
                                                       FStar_All.pipe_right
                                                         uu____3385
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            if_then_else_us) in
                                                     (if_then_else_us,
                                                       uu____3382,
                                                       if_then_else_ty)))))))))) in
              log_combinator "if_then_else" if_then_else;
              (let r =
                 let uu____3398 =
                   let uu____3401 =
                     let uu____3410 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_layered_if_then_else_combinator in
                     FStar_All.pipe_right uu____3410 FStar_Util.must in
                   FStar_All.pipe_right uu____3401
                     FStar_Pervasives_Native.snd in
                 uu____3398.FStar_Syntax_Syntax.pos in
               let binder_aq_to_arg_aq aq =
                 match aq with
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                     uu____3485) -> aq
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                     uu____3487) ->
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit false)
                 | uu____3489 -> FStar_Pervasives_Native.None in
               let uu____3492 = if_then_else in
               match uu____3492 with
               | (ite_us, ite_t, uu____3507) ->
                   let uu____3520 =
                     FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                   (match uu____3520 with
                    | (us, ite_t1) ->
                        let uu____3527 =
                          let uu____3542 =
                            let uu____3543 =
                              FStar_Syntax_Subst.compress ite_t1 in
                            uu____3543.FStar_Syntax_Syntax.n in
                          match uu____3542 with
                          | FStar_Syntax_Syntax.Tm_abs
                              (bs, uu____3561, uu____3562) ->
                              let bs1 = FStar_Syntax_Subst.open_binders bs in
                              let uu____3588 =
                                let uu____3601 =
                                  let uu____3606 =
                                    let uu____3609 =
                                      let uu____3618 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                (Prims.of_int (3)))) in
                                      FStar_All.pipe_right uu____3618
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____3609
                                      (FStar_List.map
                                         FStar_Pervasives_Native.fst) in
                                  FStar_All.pipe_right uu____3606
                                    (FStar_List.map
                                       FStar_Syntax_Syntax.bv_to_name) in
                                FStar_All.pipe_right uu____3601
                                  (fun l ->
                                     let uu____3774 = l in
                                     match uu____3774 with
                                     | f::g::p::[] -> (f, g, p)) in
                              (match uu____3588 with
                               | (f, g, p) ->
                                   let uu____3843 =
                                     let uu____3844 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     FStar_TypeChecker_Env.push_binders
                                       uu____3844 bs1 in
                                   let uu____3845 =
                                     let uu____3846 =
                                       FStar_All.pipe_right bs1
                                         (FStar_List.map
                                            (fun uu____3871 ->
                                               match uu____3871 with
                                               | (b, qual) ->
                                                   let uu____3890 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       b in
                                                   (uu____3890,
                                                     (binder_aq_to_arg_aq
                                                        qual)))) in
                                     FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                       uu____3846 r in
                                   (uu____3843, uu____3845, f, g, p))
                          | uu____3897 ->
                              failwith
                                "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                        (match uu____3527 with
                         | (env, ite_t_applied, f_t, g_t, p_t) ->
                             let uu____3926 =
                               let uu____3935 = stronger_repr in
                               match uu____3935 with
                               | (uu____3956, subcomp_t, subcomp_ty) ->
                                   let uu____3971 =
                                     FStar_Syntax_Subst.open_univ_vars us
                                       subcomp_t in
                                   (match uu____3971 with
                                    | (uu____3984, subcomp_t1) ->
                                        let uu____3986 =
                                          let uu____3997 =
                                            FStar_Syntax_Subst.open_univ_vars
                                              us subcomp_ty in
                                          match uu____3997 with
                                          | (uu____4012, subcomp_ty1) ->
                                              let uu____4014 =
                                                let uu____4015 =
                                                  FStar_Syntax_Subst.compress
                                                    subcomp_ty1 in
                                                uu____4015.FStar_Syntax_Syntax.n in
                                              (match uu____4014 with
                                               | FStar_Syntax_Syntax.Tm_arrow
                                                   (bs, uu____4029) ->
                                                   let uu____4050 =
                                                     FStar_All.pipe_right bs
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs)
                                                             - Prims.int_one)) in
                                                   (match uu____4050 with
                                                    | (bs_except_last,
                                                       last_b) ->
                                                        let uu____4156 =
                                                          FStar_All.pipe_right
                                                            bs_except_last
                                                            (FStar_List.map
                                                               FStar_Pervasives_Native.snd) in
                                                        let uu____4183 =
                                                          let uu____4186 =
                                                            FStar_All.pipe_right
                                                              last_b
                                                              FStar_List.hd in
                                                          FStar_All.pipe_right
                                                            uu____4186
                                                            FStar_Pervasives_Native.snd in
                                                        (uu____4156,
                                                          uu____4183))
                                               | uu____4229 ->
                                                   failwith
                                                     "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                        (match uu____3986 with
                                         | (aqs_except_last, last_aq) ->
                                             let uu____4263 =
                                               let uu____4274 =
                                                 FStar_All.pipe_right
                                                   aqs_except_last
                                                   (FStar_List.map
                                                      binder_aq_to_arg_aq) in
                                               let uu____4291 =
                                                 FStar_All.pipe_right last_aq
                                                   binder_aq_to_arg_aq in
                                               (uu____4274, uu____4291) in
                                             (match uu____4263 with
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
                                                  let uu____4403 = aux f_t in
                                                  let uu____4406 = aux g_t in
                                                  (uu____4403, uu____4406)))) in
                             (match uu____3926 with
                              | (subcomp_f, subcomp_g) ->
                                  let uu____4423 =
                                    let aux t =
                                      let uu____4440 =
                                        let uu____4441 =
                                          let uu____4468 =
                                            let uu____4485 =
                                              let uu____4494 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  ite_t_applied in
                                              FStar_Util.Inr uu____4494 in
                                            (uu____4485,
                                              FStar_Pervasives_Native.None) in
                                          (t, uu____4468,
                                            FStar_Pervasives_Native.None) in
                                        FStar_Syntax_Syntax.Tm_ascribed
                                          uu____4441 in
                                      FStar_Syntax_Syntax.mk uu____4440 r in
                                    let uu____4535 = aux subcomp_f in
                                    let uu____4536 = aux subcomp_g in
                                    (uu____4535, uu____4536) in
                                  (match uu____4423 with
                                   | (tm_subcomp_ascribed_f,
                                      tm_subcomp_ascribed_g) ->
                                       ((let uu____4540 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____4540
                                         then
                                           let uu____4545 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_f in
                                           let uu____4547 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_g in
                                           FStar_Util.print2
                                             "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                             uu____4545 uu____4547
                                         else ());
                                        (let uu____4552 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env tm_subcomp_ascribed_f in
                                         match uu____4552 with
                                         | (uu____4559, uu____4560, g_f) ->
                                             let g_f1 =
                                               let uu____4563 =
                                                 FStar_TypeChecker_Env.guard_of_guard_formula
                                                   (FStar_TypeChecker_Common.NonTrivial
                                                      p_t) in
                                               FStar_TypeChecker_Env.imp_guard
                                                 uu____4563 g_f in
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env g_f1;
                                              (let uu____4565 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env tm_subcomp_ascribed_g in
                                               match uu____4565 with
                                               | (uu____4572, uu____4573,
                                                  g_g) ->
                                                   let g_g1 =
                                                     let not_p =
                                                       let uu____4577 =
                                                         let uu____4578 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             FStar_Parser_Const.not_lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             FStar_Pervasives_Native.None in
                                                         FStar_All.pipe_right
                                                           uu____4578
                                                           FStar_Syntax_Syntax.fv_to_tm in
                                                       let uu____4579 =
                                                         let uu____4580 =
                                                           FStar_All.pipe_right
                                                             p_t
                                                             FStar_Syntax_Syntax.as_arg in
                                                         [uu____4580] in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____4577
                                                         uu____4579 r in
                                                     let uu____4613 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         (FStar_TypeChecker_Common.NonTrivial
                                                            not_p) in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____4613 g_g in
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
                   (let uu____4637 =
                      let uu____4643 =
                        let uu____4645 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____4647 =
                          FStar_Ident.string_of_lid
                            act.FStar_Syntax_Syntax.action_name in
                        let uu____4649 =
                          FStar_Syntax_Print.binders_to_string "; "
                            act.FStar_Syntax_Syntax.action_params in
                        FStar_Util.format3
                          "Action %s:%s has non-empty action params (%s)"
                          uu____4645 uu____4647 uu____4649 in
                      (FStar_Errors.Fatal_MalformedActionDeclaration,
                        uu____4643) in
                    FStar_Errors.raise_error uu____4637 r)
                 else ();
                 (let uu____4656 =
                    let uu____4661 =
                      FStar_Syntax_Subst.univ_var_opening
                        act.FStar_Syntax_Syntax.action_univs in
                    match uu____4661 with
                    | (usubst, us) ->
                        let uu____4684 =
                          FStar_TypeChecker_Env.push_univ_vars env us in
                        let uu____4685 =
                          let uu___450_4686 = act in
                          let uu____4687 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_defn in
                          let uu____4688 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_typ in
                          {
                            FStar_Syntax_Syntax.action_name =
                              (uu___450_4686.FStar_Syntax_Syntax.action_name);
                            FStar_Syntax_Syntax.action_unqualified_name =
                              (uu___450_4686.FStar_Syntax_Syntax.action_unqualified_name);
                            FStar_Syntax_Syntax.action_univs = us;
                            FStar_Syntax_Syntax.action_params =
                              (uu___450_4686.FStar_Syntax_Syntax.action_params);
                            FStar_Syntax_Syntax.action_defn = uu____4687;
                            FStar_Syntax_Syntax.action_typ = uu____4688
                          } in
                        (uu____4684, uu____4685) in
                  match uu____4656 with
                  | (env1, act1) ->
                      let act_typ =
                        let uu____4692 =
                          let uu____4693 =
                            FStar_Syntax_Subst.compress
                              act1.FStar_Syntax_Syntax.action_typ in
                          uu____4693.FStar_Syntax_Syntax.n in
                        match uu____4692 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                            let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                            let uu____4719 =
                              FStar_Ident.lid_equals
                                ct.FStar_Syntax_Syntax.effect_name
                                ed.FStar_Syntax_Syntax.mname in
                            if uu____4719
                            then
                              let repr_ts =
                                let uu____4723 = repr in
                                match uu____4723 with
                                | (us, t, uu____4738) -> (us, t) in
                              let repr1 =
                                let uu____4756 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts ct.FStar_Syntax_Syntax.comp_univs in
                                FStar_All.pipe_right uu____4756
                                  FStar_Pervasives_Native.snd in
                              let repr2 =
                                let uu____4766 =
                                  let uu____4767 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ in
                                  uu____4767 ::
                                    (ct.FStar_Syntax_Syntax.effect_args) in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____4766 r in
                              let c1 =
                                let uu____4785 =
                                  let uu____4788 =
                                    FStar_TypeChecker_Env.new_u_univ () in
                                  FStar_Pervasives_Native.Some uu____4788 in
                                FStar_Syntax_Syntax.mk_Total' repr2
                                  uu____4785 in
                              FStar_Syntax_Util.arrow bs c1
                            else act1.FStar_Syntax_Syntax.action_typ
                        | uu____4791 -> act1.FStar_Syntax_Syntax.action_typ in
                      let uu____4792 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          act_typ in
                      (match uu____4792 with
                       | (act_typ1, uu____4800, g_t) ->
                           let uu____4802 =
                             let uu____4809 =
                               let uu___475_4810 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   act_typ1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___475_4810.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___475_4810.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___475_4810.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___475_4810.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___475_4810.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___475_4810.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___475_4810.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___475_4810.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___475_4810.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___475_4810.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   false;
                                 FStar_TypeChecker_Env.effects =
                                   (uu___475_4810.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___475_4810.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___475_4810.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___475_4810.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___475_4810.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___475_4810.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___475_4810.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___475_4810.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___475_4810.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___475_4810.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___475_4810.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___475_4810.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___475_4810.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___475_4810.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___475_4810.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___475_4810.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___475_4810.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___475_4810.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___475_4810.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___475_4810.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___475_4810.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___475_4810.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___475_4810.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___475_4810.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___475_4810.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___475_4810.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___475_4810.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___475_4810.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___475_4810.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___475_4810.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___475_4810.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___475_4810.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___475_4810.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___475_4810.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___475_4810.FStar_TypeChecker_Env.erasable_types_tab);
                                 FStar_TypeChecker_Env.enable_defer_to_tac =
                                   (uu___475_4810.FStar_TypeChecker_Env.enable_defer_to_tac)
                               } in
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu____4809
                               act1.FStar_Syntax_Syntax.action_defn in
                           (match uu____4802 with
                            | (act_defn, uu____4813, g_d) ->
                                ((let uu____4816 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "LayeredEffectsTc") in
                                  if uu____4816
                                  then
                                    let uu____4821 =
                                      FStar_Syntax_Print.term_to_string
                                        act_defn in
                                    let uu____4823 =
                                      FStar_Syntax_Print.term_to_string
                                        act_typ1 in
                                    FStar_Util.print2
                                      "Typechecked action definition: %s and action type: %s\n"
                                      uu____4821 uu____4823
                                  else ());
                                 (let uu____4828 =
                                    let act_typ2 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        act_typ1 in
                                    let uu____4836 =
                                      let uu____4837 =
                                        FStar_Syntax_Subst.compress act_typ2 in
                                      uu____4837.FStar_Syntax_Syntax.n in
                                    match uu____4836 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____4847) ->
                                        let bs1 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        let env2 =
                                          FStar_TypeChecker_Env.push_binders
                                            env1 bs1 in
                                        let uu____4870 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____4870 with
                                         | (t, u) ->
                                             let reason =
                                               let uu____4885 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____4887 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               FStar_Util.format2
                                                 "implicit for return type of action %s:%s"
                                                 uu____4885 uu____4887 in
                                             let uu____4890 =
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r env2 t in
                                             (match uu____4890 with
                                              | (a_tm, uu____4910, g_tm) ->
                                                  let uu____4924 =
                                                    fresh_repr r env2 u a_tm in
                                                  (match uu____4924 with
                                                   | (repr1, g) ->
                                                       let uu____4937 =
                                                         let uu____4940 =
                                                           let uu____4943 =
                                                             let uu____4946 =
                                                               FStar_TypeChecker_Env.new_u_univ
                                                                 () in
                                                             FStar_All.pipe_right
                                                               uu____4946
                                                               (fun
                                                                  uu____4949
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____4949) in
                                                           FStar_Syntax_Syntax.mk_Total'
                                                             repr1 uu____4943 in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____4940 in
                                                       let uu____4950 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g g_tm in
                                                       (uu____4937,
                                                         uu____4950))))
                                    | uu____4953 ->
                                        let uu____4954 =
                                          let uu____4960 =
                                            let uu____4962 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____4964 =
                                              FStar_Ident.string_of_lid
                                                act1.FStar_Syntax_Syntax.action_name in
                                            let uu____4966 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.format3
                                              "Unexpected non-function type for action %s:%s (%s)"
                                              uu____4962 uu____4964
                                              uu____4966 in
                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                            uu____4960) in
                                        FStar_Errors.raise_error uu____4954 r in
                                  match uu____4828 with
                                  | (k, g_k) ->
                                      ((let uu____4983 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsTc") in
                                        if uu____4983
                                        then
                                          let uu____4988 =
                                            FStar_Syntax_Print.term_to_string
                                              k in
                                          FStar_Util.print1
                                            "Expected action type: %s\n"
                                            uu____4988
                                        else ());
                                       (let g =
                                          FStar_TypeChecker_Rel.teq env1
                                            act_typ1 k in
                                        FStar_List.iter
                                          (FStar_TypeChecker_Rel.force_trivial_guard
                                             env1) [g_t; g_d; g_k; g];
                                        (let uu____4996 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____4996
                                         then
                                           let uu____5001 =
                                             FStar_Syntax_Print.term_to_string
                                               k in
                                           FStar_Util.print1
                                             "Expected action type after unification: %s\n"
                                             uu____5001
                                         else ());
                                        (let act_typ2 =
                                           let err_msg t =
                                             let uu____5014 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             let uu____5016 =
                                               FStar_Ident.string_of_lid
                                                 act1.FStar_Syntax_Syntax.action_name in
                                             let uu____5018 =
                                               FStar_Syntax_Print.term_to_string
                                                 t in
                                             FStar_Util.format3
                                               "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                               uu____5014 uu____5016
                                               uu____5018 in
                                           let repr_args t =
                                             let uu____5039 =
                                               let uu____5040 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____5040.FStar_Syntax_Syntax.n in
                                             match uu____5039 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (head, a::is) ->
                                                 let uu____5092 =
                                                   let uu____5093 =
                                                     FStar_Syntax_Subst.compress
                                                       head in
                                                   uu____5093.FStar_Syntax_Syntax.n in
                                                 (match uu____5092 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      (uu____5102, us) ->
                                                      (us,
                                                        (FStar_Pervasives_Native.fst
                                                           a), is)
                                                  | uu____5112 ->
                                                      let uu____5113 =
                                                        let uu____5119 =
                                                          err_msg t in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____5119) in
                                                      FStar_Errors.raise_error
                                                        uu____5113 r)
                                             | uu____5128 ->
                                                 let uu____5129 =
                                                   let uu____5135 = err_msg t in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____5135) in
                                                 FStar_Errors.raise_error
                                                   uu____5129 r in
                                           let k1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 k in
                                           let uu____5145 =
                                             let uu____5146 =
                                               FStar_Syntax_Subst.compress k1 in
                                             uu____5146.FStar_Syntax_Syntax.n in
                                           match uu____5145 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, c) ->
                                               let uu____5171 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs c in
                                               (match uu____5171 with
                                                | (bs1, c1) ->
                                                    let uu____5178 =
                                                      repr_args
                                                        (FStar_Syntax_Util.comp_result
                                                           c1) in
                                                    (match uu____5178 with
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
                                                         let uu____5189 =
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             ct in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____5189))
                                           | uu____5192 ->
                                               let uu____5193 =
                                                 let uu____5199 = err_msg k1 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____5199) in
                                               FStar_Errors.raise_error
                                                 uu____5193 r in
                                         (let uu____5203 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____5203
                                          then
                                            let uu____5208 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.print1
                                              "Action type after injecting it into the monad: %s\n"
                                              uu____5208
                                          else ());
                                         (let act2 =
                                            let uu____5214 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env1 act_defn in
                                            match uu____5214 with
                                            | (us, act_defn1) ->
                                                if
                                                  act1.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then
                                                  let uu___548_5228 = act1 in
                                                  let uu____5229 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      us act_typ2 in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___548_5228.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___548_5228.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      = us;
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___548_5228.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____5229
                                                  }
                                                else
                                                  (let uu____5232 =
                                                     ((FStar_List.length us)
                                                        =
                                                        (FStar_List.length
                                                           act1.FStar_Syntax_Syntax.action_univs))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1 ->
                                                             fun u2 ->
                                                               let uu____5239
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2 in
                                                               uu____5239 =
                                                                 Prims.int_zero)
                                                          us
                                                          act1.FStar_Syntax_Syntax.action_univs) in
                                                   if uu____5232
                                                   then
                                                     let uu___553_5244 = act1 in
                                                     let uu____5245 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                         act_typ2 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___553_5244.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___553_5244.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         =
                                                         (uu___553_5244.FStar_Syntax_Syntax.action_univs);
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___553_5244.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = act_defn1;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5245
                                                     }
                                                   else
                                                     (let uu____5248 =
                                                        let uu____5254 =
                                                          let uu____5256 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname in
                                                          let uu____5258 =
                                                            FStar_Ident.string_of_lid
                                                              act1.FStar_Syntax_Syntax.action_name in
                                                          let uu____5260 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              us in
                                                          let uu____5262 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              act1.FStar_Syntax_Syntax.action_univs in
                                                          FStar_Util.format4
                                                            "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                            uu____5256
                                                            uu____5258
                                                            uu____5260
                                                            uu____5262 in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____5254) in
                                                      FStar_Errors.raise_error
                                                        uu____5248 r)) in
                                          act2))))))))) in
               let tschemes_of uu____5287 =
                 match uu____5287 with | (us, t, ty) -> ((us, t), (us, ty)) in
               let combinators =
                 let uu____5332 =
                   let uu____5333 = tschemes_of repr in
                   let uu____5338 = tschemes_of return_repr in
                   let uu____5343 = tschemes_of bind_repr in
                   let uu____5348 = tschemes_of stronger_repr in
                   let uu____5353 = tschemes_of if_then_else in
                   {
                     FStar_Syntax_Syntax.l_repr = uu____5333;
                     FStar_Syntax_Syntax.l_return = uu____5338;
                     FStar_Syntax_Syntax.l_bind = uu____5343;
                     FStar_Syntax_Syntax.l_subcomp = uu____5348;
                     FStar_Syntax_Syntax.l_if_then_else = uu____5353
                   } in
                 FStar_Syntax_Syntax.Layered_eff uu____5332 in
               let uu___562_5358 = ed in
               let uu____5359 =
                 FStar_List.map (tc_action env0)
                   ed.FStar_Syntax_Syntax.actions in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___562_5358.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___562_5358.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs =
                   (uu___562_5358.FStar_Syntax_Syntax.univs);
                 FStar_Syntax_Syntax.binders =
                   (uu___562_5358.FStar_Syntax_Syntax.binders);
                 FStar_Syntax_Syntax.signature =
                   (let uu____5366 = signature in
                    match uu____5366 with | (us, t, uu____5381) -> (us, t));
                 FStar_Syntax_Syntax.combinators = combinators;
                 FStar_Syntax_Syntax.actions = uu____5359;
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___562_5358.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5419 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED") in
         if uu____5419
         then
           let uu____5424 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5424
         else ());
        (let uu____5430 =
           let uu____5435 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
           match uu____5435 with
           | (ed_univs_subst, ed_univs) ->
               let bs =
                 let uu____5459 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders in
                 FStar_Syntax_Subst.open_binders uu____5459 in
               let uu____5460 =
                 let uu____5467 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5467 bs in
               (match uu____5460 with
                | (bs1, uu____5473, uu____5474) ->
                    let uu____5475 =
                      let tmp_t =
                        let uu____5485 =
                          let uu____5488 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5493 ->
                                 FStar_Pervasives_Native.Some uu____5493) in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5488 in
                        FStar_Syntax_Util.arrow bs1 uu____5485 in
                      let uu____5494 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t in
                      match uu____5494 with
                      | (us, tmp_t1) ->
                          let uu____5511 =
                            let uu____5512 =
                              let uu____5513 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals in
                              FStar_All.pipe_right uu____5513
                                FStar_Pervasives_Native.fst in
                            FStar_All.pipe_right uu____5512
                              FStar_Syntax_Subst.close_binders in
                          (us, uu____5511) in
                    (match uu____5475 with
                     | (us, bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5550 ->
                              let uu____5553 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1 ->
                                        fun u2 ->
                                          let uu____5560 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2 in
                                          uu____5560 = Prims.int_zero)
                                     ed_univs us) in
                              if uu____5553
                              then (us, bs2)
                              else
                                (let uu____5571 =
                                   let uu____5577 =
                                     let uu____5579 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname in
                                     let uu____5581 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs) in
                                     let uu____5583 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us) in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5579 uu____5581 uu____5583 in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5577) in
                                 let uu____5587 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Errors.raise_error uu____5571
                                   uu____5587)))) in
         match uu____5430 with
         | (us, bs) ->
             let ed1 =
               let uu___596_5595 = ed in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___596_5595.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___596_5595.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___596_5595.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___596_5595.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___596_5595.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___596_5595.FStar_Syntax_Syntax.eff_attrs)
               } in
             let uu____5596 = FStar_Syntax_Subst.univ_var_opening us in
             (match uu____5596 with
              | (ed_univs_subst, ed_univs) ->
                  let uu____5615 =
                    let uu____5620 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                    FStar_Syntax_Subst.open_binders' uu____5620 in
                  (match uu____5615 with
                   | (ed_bs, ed_bs_subst) ->
                       let ed2 =
                         let op uu____5641 =
                           match uu____5641 with
                           | (us1, t) ->
                               let t1 =
                                 let uu____5661 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst in
                                 FStar_Syntax_Subst.subst uu____5661 t in
                               let uu____5670 =
                                 let uu____5671 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst in
                                 FStar_Syntax_Subst.subst uu____5671 t1 in
                               (us1, uu____5670) in
                         let uu___610_5676 = ed1 in
                         let uu____5677 =
                           op ed1.FStar_Syntax_Syntax.signature in
                         let uu____5678 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators in
                         let uu____5679 =
                           FStar_List.map
                             (fun a ->
                                let uu___613_5687 = a in
                                let uu____5688 =
                                  let uu____5689 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn)) in
                                  FStar_Pervasives_Native.snd uu____5689 in
                                let uu____5700 =
                                  let uu____5701 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ)) in
                                  FStar_Pervasives_Native.snd uu____5701 in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___613_5687.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___613_5687.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___613_5687.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___613_5687.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5688;
                                  FStar_Syntax_Syntax.action_typ = uu____5700
                                }) ed1.FStar_Syntax_Syntax.actions in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___610_5676.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___610_5676.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___610_5676.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___610_5676.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5677;
                           FStar_Syntax_Syntax.combinators = uu____5678;
                           FStar_Syntax_Syntax.actions = uu____5679;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___610_5676.FStar_Syntax_Syntax.eff_attrs)
                         } in
                       ((let uu____5713 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED") in
                         if uu____5713
                         then
                           let uu____5718 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2 in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5718
                         else ());
                        (let env =
                           let uu____5725 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs in
                           FStar_TypeChecker_Env.push_binders uu____5725
                             ed_bs in
                         let check_and_gen' comb n env_opt uu____5760 k =
                           match uu____5760 with
                           | (us1, t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env in
                               let uu____5780 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t in
                               (match uu____5780 with
                                | (us2, t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5789 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2 in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5789 t1 k1
                                      | FStar_Pervasives_Native.None ->
                                          let uu____5790 =
                                            let uu____5797 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5797 t1 in
                                          (match uu____5790 with
                                           | (t2, uu____5799, g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2)) in
                                    let uu____5802 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2 in
                                    (match uu____5802 with
                                     | (g_us, t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5818 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname in
                                               let uu____5820 =
                                                 FStar_Util.string_of_int n in
                                               let uu____5822 =
                                                 let uu____5824 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length in
                                                 FStar_All.pipe_right
                                                   uu____5824
                                                   FStar_Util.string_of_int in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5818 comb uu____5820
                                                 uu____5822 in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5839 ->
                                               let uu____5840 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____5847 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____5847 =
                                                             Prims.int_zero)
                                                      us2 g_us) in
                                               if uu____5840
                                               then (g_us, t3)
                                               else
                                                 (let uu____5858 =
                                                    let uu____5864 =
                                                      let uu____5866 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____5868 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2) in
                                                      let uu____5870 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us) in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5866 comb
                                                        uu____5868 uu____5870 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5864) in
                                                  FStar_Errors.raise_error
                                                    uu____5858
                                                    t3.FStar_Syntax_Syntax.pos))))) in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None in
                         (let uu____5878 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED") in
                          if uu____5878
                          then
                            let uu____5883 =
                              FStar_Syntax_Print.tscheme_to_string signature in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5883
                          else ());
                         (let fresh_a_and_wp uu____5899 =
                            let fail t =
                              let uu____5912 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t in
                              FStar_Errors.raise_error uu____5912
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                            let uu____5928 =
                              FStar_TypeChecker_Env.inst_tscheme signature in
                            match uu____5928 with
                            | (uu____5939, signature1) ->
                                let uu____5941 =
                                  let uu____5942 =
                                    FStar_Syntax_Subst.compress signature1 in
                                  uu____5942.FStar_Syntax_Syntax.n in
                                (match uu____5941 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1, uu____5952) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1 in
                                     (match bs2 with
                                      | (a, uu____5981)::(wp, uu____5983)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____6012 -> fail signature1)
                                 | uu____6013 -> fail signature1) in
                          let log_combinator s ts =
                            let uu____6027 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED") in
                            if uu____6027
                            then
                              let uu____6032 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname in
                              let uu____6034 =
                                FStar_Syntax_Print.tscheme_to_string ts in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____6032 s uu____6034
                            else () in
                          let ret_wp =
                            let uu____6040 = fresh_a_and_wp () in
                            match uu____6040 with
                            | (a, wp_sort) ->
                                let k =
                                  let uu____6056 =
                                    let uu____6065 =
                                      FStar_Syntax_Syntax.mk_binder a in
                                    let uu____6072 =
                                      let uu____6081 =
                                        let uu____6088 =
                                          FStar_Syntax_Syntax.bv_to_name a in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____6088 in
                                      [uu____6081] in
                                    uu____6065 :: uu____6072 in
                                  let uu____6107 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                  FStar_Syntax_Util.arrow uu____6056
                                    uu____6107 in
                                let uu____6110 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____6110
                                  (FStar_Pervasives_Native.Some k) in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____6124 = fresh_a_and_wp () in
                             match uu____6124 with
                             | (a, wp_sort_a) ->
                                 let uu____6137 = fresh_a_and_wp () in
                                 (match uu____6137 with
                                  | (b, wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____6153 =
                                          let uu____6162 =
                                            let uu____6169 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____6169 in
                                          [uu____6162] in
                                        let uu____6182 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____6153
                                          uu____6182 in
                                      let k =
                                        let uu____6188 =
                                          let uu____6197 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____6204 =
                                            let uu____6213 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____6220 =
                                              let uu____6229 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____6236 =
                                                let uu____6245 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a in
                                                let uu____6252 =
                                                  let uu____6261 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b in
                                                  [uu____6261] in
                                                uu____6245 :: uu____6252 in
                                              uu____6229 :: uu____6236 in
                                            uu____6213 :: uu____6220 in
                                          uu____6197 :: uu____6204 in
                                        let uu____6304 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____6188
                                          uu____6304 in
                                      let uu____6307 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6307
                                        (FStar_Pervasives_Native.Some k)) in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6321 = fresh_a_and_wp () in
                              match uu____6321 with
                              | (a, wp_sort_a) ->
                                  let uu____6334 =
                                    FStar_Syntax_Util.type_u () in
                                  (match uu____6334 with
                                   | (t, uu____6340) ->
                                       let k =
                                         let uu____6344 =
                                           let uu____6353 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____6360 =
                                             let uu____6369 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____6376 =
                                               let uu____6385 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____6385] in
                                             uu____6369 :: uu____6376 in
                                           uu____6353 :: uu____6360 in
                                         let uu____6416 =
                                           FStar_Syntax_Syntax.mk_Total t in
                                         FStar_Syntax_Util.arrow uu____6344
                                           uu____6416 in
                                       let uu____6419 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6419
                                         (FStar_Pervasives_Native.Some k)) in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6433 = fresh_a_and_wp () in
                               match uu____6433 with
                               | (a, wp_sort_a) ->
                                   let p =
                                     let uu____6447 =
                                       let uu____6450 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname in
                                       FStar_Pervasives_Native.Some
                                         uu____6450 in
                                     let uu____6451 =
                                       let uu____6452 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____6452
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.new_bv uu____6447
                                       uu____6451 in
                                   let k =
                                     let uu____6464 =
                                       let uu____6473 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____6480 =
                                         let uu____6489 =
                                           FStar_Syntax_Syntax.mk_binder p in
                                         let uu____6496 =
                                           let uu____6505 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a in
                                           let uu____6512 =
                                             let uu____6521 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             [uu____6521] in
                                           uu____6505 :: uu____6512 in
                                         uu____6489 :: uu____6496 in
                                       uu____6473 :: uu____6480 in
                                     let uu____6558 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a in
                                     FStar_Syntax_Util.arrow uu____6464
                                       uu____6558 in
                                   let uu____6561 =
                                     let uu____6566 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                     FStar_All.pipe_right uu____6566
                                       FStar_Util.must in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6561
                                     (FStar_Pervasives_Native.Some k) in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6598 = fresh_a_and_wp () in
                                match uu____6598 with
                                | (a, wp_sort_a) ->
                                    let k =
                                      let uu____6614 =
                                        let uu____6623 =
                                          FStar_Syntax_Syntax.mk_binder a in
                                        let uu____6630 =
                                          let uu____6639 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a in
                                          [uu____6639] in
                                        uu____6623 :: uu____6630 in
                                      let uu____6664 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a in
                                      FStar_Syntax_Util.arrow uu____6614
                                        uu____6664 in
                                    let uu____6667 =
                                      let uu____6672 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator in
                                      FStar_All.pipe_right uu____6672
                                        FStar_Util.must in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6667
                                      (FStar_Pervasives_Native.Some k) in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6688 = fresh_a_and_wp () in
                                 match uu____6688 with
                                 | (a, wp_sort_a) ->
                                     let b =
                                       let uu____6702 =
                                         let uu____6705 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____6705 in
                                       let uu____6706 =
                                         let uu____6707 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____6707
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____6702
                                         uu____6706 in
                                     let wp_sort_b_a =
                                       let uu____6719 =
                                         let uu____6728 =
                                           let uu____6735 =
                                             FStar_Syntax_Syntax.bv_to_name b in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6735 in
                                         [uu____6728] in
                                       let uu____6748 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____6719
                                         uu____6748 in
                                     let k =
                                       let uu____6754 =
                                         let uu____6763 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____6770 =
                                           let uu____6779 =
                                             FStar_Syntax_Syntax.mk_binder b in
                                           let uu____6786 =
                                             let uu____6795 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a in
                                             [uu____6795] in
                                           uu____6779 :: uu____6786 in
                                         uu____6763 :: uu____6770 in
                                       let uu____6826 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____6754
                                         uu____6826 in
                                     let uu____6829 =
                                       let uu____6834 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator in
                                       FStar_All.pipe_right uu____6834
                                         FStar_Util.must in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6829
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6850 = fresh_a_and_wp () in
                                  match uu____6850 with
                                  | (a, wp_sort_a) ->
                                      let uu____6863 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____6863 with
                                       | (t, uu____6869) ->
                                           let k =
                                             let uu____6873 =
                                               let uu____6882 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____6889 =
                                                 let uu____6898 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____6898] in
                                               uu____6882 :: uu____6889 in
                                             let uu____6923 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t in
                                             FStar_Syntax_Util.arrow
                                               uu____6873 uu____6923 in
                                           let trivial =
                                             let uu____6927 =
                                               let uu____6932 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator in
                                               FStar_All.pipe_right
                                                 uu____6932 FStar_Util.must in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6927
                                               (FStar_Pervasives_Native.Some
                                                  k) in
                                           (log_combinator "trivial" trivial;
                                            trivial)) in
                                let uu____6947 =
                                  let uu____6964 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr in
                                  match uu____6964 with
                                  | FStar_Pervasives_Native.None ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6993 ->
                                      let repr =
                                        let uu____6997 = fresh_a_and_wp () in
                                        match uu____6997 with
                                        | (a, wp_sort_a) ->
                                            let uu____7010 =
                                              FStar_Syntax_Util.type_u () in
                                            (match uu____7010 with
                                             | (t, uu____7016) ->
                                                 let k =
                                                   let uu____7020 =
                                                     let uu____7029 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a in
                                                     let uu____7036 =
                                                       let uu____7045 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       [uu____7045] in
                                                     uu____7029 :: uu____7036 in
                                                   let uu____7070 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t in
                                                   FStar_Syntax_Util.arrow
                                                     uu____7020 uu____7070 in
                                                 let uu____7073 =
                                                   let uu____7078 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr in
                                                   FStar_All.pipe_right
                                                     uu____7078
                                                     FStar_Util.must in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____7073
                                                   (FStar_Pervasives_Native.Some
                                                      k)) in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____7122 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr in
                                          match uu____7122 with
                                          | (uu____7129, repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1 in
                                              let uu____7132 =
                                                let uu____7133 =
                                                  let uu____7150 =
                                                    let uu____7161 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____7178 =
                                                      let uu____7189 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____7189] in
                                                    uu____7161 :: uu____7178 in
                                                  (repr2, uu____7150) in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____7133 in
                                              FStar_Syntax_Syntax.mk
                                                uu____7132
                                                FStar_Range.dummyRange in
                                        let mk_repr a wp =
                                          let uu____7255 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          mk_repr' uu____7255 wp in
                                        let destruct_repr t =
                                          let uu____7270 =
                                            let uu____7271 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____7271.FStar_Syntax_Syntax.n in
                                          match uu____7270 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7282,
                                               (t1, uu____7284)::(wp,
                                                                  uu____7286)::[])
                                              -> (t1, wp)
                                          | uu____7345 ->
                                              failwith "Unexpected repr type" in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7361 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr in
                                            FStar_All.pipe_right uu____7361
                                              FStar_Util.must in
                                          let uu____7388 = fresh_a_and_wp () in
                                          match uu____7388 with
                                          | (a, uu____7396) ->
                                              let x_a =
                                                let uu____7402 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7402 in
                                              let res =
                                                let wp =
                                                  let uu____7408 =
                                                    let uu____7409 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp in
                                                    FStar_All.pipe_right
                                                      uu____7409
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____7418 =
                                                    let uu____7419 =
                                                      let uu____7428 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_All.pipe_right
                                                        uu____7428
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____7437 =
                                                      let uu____7448 =
                                                        let uu____7457 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a in
                                                        FStar_All.pipe_right
                                                          uu____7457
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____7448] in
                                                    uu____7419 :: uu____7437 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7408 uu____7418
                                                    FStar_Range.dummyRange in
                                                mk_repr a wp in
                                              let k =
                                                let uu____7493 =
                                                  let uu____7502 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____7509 =
                                                    let uu____7518 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a in
                                                    [uu____7518] in
                                                  uu____7502 :: uu____7509 in
                                                let uu____7543 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res in
                                                FStar_Syntax_Util.arrow
                                                  uu____7493 uu____7543 in
                                              let uu____7546 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k in
                                              (match uu____7546 with
                                               | (k1, uu____7554, uu____7555)
                                                   ->
                                                   let env1 =
                                                     let uu____7559 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7559 in
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
                                             let uu____7572 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr in
                                             FStar_All.pipe_right uu____7572
                                               FStar_Util.must in
                                           let r =
                                             let uu____7610 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None in
                                             FStar_All.pipe_right uu____7610
                                               FStar_Syntax_Syntax.fv_to_tm in
                                           let uu____7611 = fresh_a_and_wp () in
                                           match uu____7611 with
                                           | (a, wp_sort_a) ->
                                               let uu____7624 =
                                                 fresh_a_and_wp () in
                                               (match uu____7624 with
                                                | (b, wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7640 =
                                                        let uu____7649 =
                                                          let uu____7656 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7656 in
                                                        [uu____7649] in
                                                      let uu____7669 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7640 uu____7669 in
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
                                                      let uu____7677 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7677 in
                                                    let wp_g_x =
                                                      let uu____7680 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g in
                                                      let uu____7681 =
                                                        let uu____7682 =
                                                          let uu____7691 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____7691
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____7682] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7680 uu____7681
                                                        FStar_Range.dummyRange in
                                                    let res =
                                                      let wp =
                                                        let uu____7720 =
                                                          let uu____7721 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp in
                                                          FStar_All.pipe_right
                                                            uu____7721
                                                            FStar_Pervasives_Native.snd in
                                                        let uu____7730 =
                                                          let uu____7731 =
                                                            let uu____7734 =
                                                              let uu____7737
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a in
                                                              let uu____7738
                                                                =
                                                                let uu____7741
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                let uu____7742
                                                                  =
                                                                  let uu____7745
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  let uu____7746
                                                                    =
                                                                    let uu____7749
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____7749] in
                                                                  uu____7745
                                                                    ::
                                                                    uu____7746 in
                                                                uu____7741 ::
                                                                  uu____7742 in
                                                              uu____7737 ::
                                                                uu____7738 in
                                                            r :: uu____7734 in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7731 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7720
                                                          uu____7730
                                                          FStar_Range.dummyRange in
                                                      mk_repr b wp in
                                                    let maybe_range_arg =
                                                      let uu____7767 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs in
                                                      if uu____7767
                                                      then
                                                        let uu____7778 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range in
                                                        let uu____7785 =
                                                          let uu____7794 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          [uu____7794] in
                                                        uu____7778 ::
                                                          uu____7785
                                                      else [] in
                                                    let k =
                                                      let uu____7830 =
                                                        let uu____7839 =
                                                          let uu____7848 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a in
                                                          let uu____7855 =
                                                            let uu____7864 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b in
                                                            [uu____7864] in
                                                          uu____7848 ::
                                                            uu____7855 in
                                                        let uu____7889 =
                                                          let uu____7898 =
                                                            let uu____7907 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f in
                                                            let uu____7914 =
                                                              let uu____7923
                                                                =
                                                                let uu____7930
                                                                  =
                                                                  let uu____7931
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  mk_repr a
                                                                    uu____7931 in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7930 in
                                                              let uu____7932
                                                                =
                                                                let uu____7941
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                let uu____7948
                                                                  =
                                                                  let uu____7957
                                                                    =
                                                                    let uu____7964
                                                                    =
                                                                    let uu____7965
                                                                    =
                                                                    let uu____7974
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____7974] in
                                                                    let uu____7993
                                                                    =
                                                                    let uu____7996
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7996 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7965
                                                                    uu____7993 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7964 in
                                                                  [uu____7957] in
                                                                uu____7941 ::
                                                                  uu____7948 in
                                                              uu____7923 ::
                                                                uu____7932 in
                                                            uu____7907 ::
                                                              uu____7914 in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7898 in
                                                        FStar_List.append
                                                          uu____7839
                                                          uu____7889 in
                                                      let uu____8041 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7830 uu____8041 in
                                                    let uu____8044 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k in
                                                    (match uu____8044 with
                                                     | (k1, uu____8052,
                                                        uu____8053) ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___808_8063
                                                                = env1 in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___808_8063.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____8065
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____8065) in
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
                                              (let uu____8092 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____8106 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs in
                                                    match uu____8106 with
                                                    | (usubst, uvs) ->
                                                        let uu____8129 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs in
                                                        let uu____8130 =
                                                          let uu___821_8131 =
                                                            act in
                                                          let uu____8132 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn in
                                                          let uu____8133 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___821_8131.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___821_8131.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___821_8131.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____8132;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____8133
                                                          } in
                                                        (uu____8129,
                                                          uu____8130)) in
                                               match uu____8092 with
                                               | (env1, act1) ->
                                                   let act_typ =
                                                     let uu____8137 =
                                                       let uu____8138 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                       uu____8138.FStar_Syntax_Syntax.n in
                                                     match uu____8137 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1, c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c in
                                                         let uu____8164 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname in
                                                         if uu____8164
                                                         then
                                                           let uu____8167 =
                                                             let uu____8170 =
                                                               let uu____8171
                                                                 =
                                                                 let uu____8172
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____8172 in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____8171 in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____8170 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____8167
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8195 ->
                                                         act1.FStar_Syntax_Syntax.action_typ in
                                                   let uu____8196 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ in
                                                   (match uu____8196 with
                                                    | (act_typ1, uu____8204,
                                                       g_t) ->
                                                        let env' =
                                                          let uu___838_8207 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1 in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___838_8207.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          } in
                                                        ((let uu____8210 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED") in
                                                          if uu____8210
                                                          then
                                                            let uu____8214 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____8216 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            let uu____8218 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1 in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8214
                                                              uu____8216
                                                              uu____8218
                                                          else ());
                                                         (let uu____8223 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn in
                                                          match uu____8223
                                                          with
                                                          | (act_defn,
                                                             uu____8231, g_a)
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
                                                              let uu____8235
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
                                                                    let uu____8271
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____8271
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____8283)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____8290
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8290 in
                                                                    let uu____8293
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____8293
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____8307,
                                                                    g) ->
                                                                    (k1, g)))
                                                                | uu____8311
                                                                    ->
                                                                    let uu____8312
                                                                    =
                                                                    let uu____8318
                                                                    =
                                                                    let uu____8320
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____8322
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8320
                                                                    uu____8322 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8318) in
                                                                    FStar_Errors.raise_error
                                                                    uu____8312
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                              (match uu____8235
                                                               with
                                                               | (expected_k,
                                                                  g_k) ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                   ((
                                                                    let uu____8340
                                                                    =
                                                                    let uu____8341
                                                                    =
                                                                    let uu____8342
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8342 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8341 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8340);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8344
                                                                    =
                                                                    let uu____8345
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____8345.FStar_Syntax_Syntax.n in
                                                                    match uu____8344
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____8370
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____8370
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____8377
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____8377
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____8397
                                                                    =
                                                                    let uu____8398
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____8398] in
                                                                    let uu____8399
                                                                    =
                                                                    let uu____8410
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____8410] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8397;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8399;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____8435
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8435))
                                                                    | 
                                                                    uu____8438
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____8440
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8462
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8462)) in
                                                                    match uu____8440
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
                                                                    let uu___888_8481
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___888_8481.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___888_8481.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___888_8481.FStar_Syntax_Syntax.action_params);
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
                                match uu____6947 with
                                | (repr, return_repr, bind_repr, actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs in
                                      let uu____8524 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8524 ts1 in
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
                                          uu____8536 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8537 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8538 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected" in
                                    let ed3 =
                                      let uu___908_8541 = ed2 in
                                      let uu____8542 = cl signature in
                                      let uu____8543 =
                                        FStar_List.map
                                          (fun a ->
                                             let uu___911_8551 = a in
                                             let uu____8552 =
                                               let uu____8553 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn)) in
                                               FStar_All.pipe_right
                                                 uu____8553
                                                 FStar_Pervasives_Native.snd in
                                             let uu____8578 =
                                               let uu____8579 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ)) in
                                               FStar_All.pipe_right
                                                 uu____8579
                                                 FStar_Pervasives_Native.snd in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___911_8551.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___911_8551.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___911_8551.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___911_8551.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8552;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8578
                                             }) actions in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___908_8541.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___908_8541.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___908_8541.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___908_8541.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8542;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8543;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___908_8541.FStar_Syntax_Syntax.eff_attrs)
                                      } in
                                    ((let uu____8605 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED") in
                                      if uu____8605
                                      then
                                        let uu____8610 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8610
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
        let uu____8636 =
          let uu____8651 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
          if uu____8651 then tc_layered_eff_decl else tc_non_layered_eff_decl in
        uu____8636 env ed quals
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
        let fail uu____8701 =
          let uu____8702 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____8708 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____8702 uu____8708 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____8752)::(wp, uu____8754)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8783 -> fail ())
        | uu____8784 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____8797 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____8797
       then
         let uu____8802 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8802
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____8827 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____8827.FStar_Syntax_Syntax.pos in
       let uu____8840 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____8840 with
       | (us, lift, lift_ty) ->
           ((let uu____8854 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____8854
             then
               let uu____8859 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____8865 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____8859 uu____8865
             else ());
            (let uu____8874 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____8874 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____8892 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____8894 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____8896 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____8892 uu____8894 s uu____8896 in
                   let uu____8899 =
                     let uu____8906 =
                       let uu____8911 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____8911
                         (fun uu____8928 ->
                            match uu____8928 with
                            | (t, u) ->
                                let uu____8939 =
                                  let uu____8940 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____8940
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____8939, u)) in
                     match uu____8906 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____8959 =
                             let uu____8960 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____8960.FStar_Syntax_Syntax.n in
                           match uu____8959 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____8972)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____9000 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____9000 with
                                | (a', uu____9010)::bs1 ->
                                    let uu____9030 =
                                      let uu____9031 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____9031
                                        FStar_Pervasives_Native.fst in
                                    let uu____9097 =
                                      let uu____9110 =
                                        let uu____9113 =
                                          let uu____9114 =
                                            let uu____9121 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____9121) in
                                          FStar_Syntax_Syntax.NT uu____9114 in
                                        [uu____9113] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____9110 in
                                    FStar_All.pipe_right uu____9030
                                      uu____9097)
                           | uu____9136 ->
                               let uu____9137 =
                                 let uu____9143 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____9143) in
                               FStar_Errors.raise_error uu____9137 r in
                         let uu____9155 =
                           let uu____9166 =
                             let uu____9171 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____9178 =
                               let uu____9179 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____9179
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____9171 r sub.FStar_Syntax_Syntax.source
                               u_a uu____9178 in
                           match uu____9166 with
                           | (f_sort, g) ->
                               let uu____9200 =
                                 let uu____9207 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____9207
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____9200, g) in
                         (match uu____9155 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____9274 =
                                let uu____9279 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____9280 =
                                  let uu____9281 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____9281
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____9279 r sub.FStar_Syntax_Syntax.target
                                  u_a uu____9280 in
                              (match uu____9274 with
                               | (repr, g_repr) ->
                                   let uu____9298 =
                                     let uu____9303 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____9304 =
                                       let uu____9306 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____9308 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____9306 uu____9308 in
                                     pure_wp_uvar uu____9303 repr uu____9304
                                       r in
                                   (match uu____9298 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____9320 =
                                            let uu____9321 =
                                              let uu____9322 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____9322] in
                                            let uu____9323 =
                                              let uu____9334 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____9334] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____9321;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____9323;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____9320 in
                                        let uu____9367 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____9370 =
                                          let uu____9371 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____9371 guard_wp in
                                        (uu____9367, uu____9370)))) in
                   match uu____8899 with
                   | (k, g_k) ->
                       ((let uu____9381 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____9381
                         then
                           let uu____9386 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____9386
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____9395 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____9395
                          then
                            let uu____9400 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____9400
                          else ());
                         (let sub1 =
                            let uu___1000_9406 = sub in
                            let uu____9407 =
                              let uu____9410 =
                                let uu____9411 =
                                  let uu____9414 =
                                    FStar_All.pipe_right k
                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env) in
                                  FStar_All.pipe_right uu____9414
                                    (FStar_Syntax_Subst.close_univ_vars us1) in
                                (us1, uu____9411) in
                              FStar_Pervasives_Native.Some uu____9410 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___1000_9406.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___1000_9406.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = uu____9407;
                              FStar_Syntax_Syntax.lift =
                                (FStar_Pervasives_Native.Some (us1, lift))
                            } in
                          (let uu____9426 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffectsTc") in
                           if uu____9426
                           then
                             let uu____9431 =
                               FStar_Syntax_Print.sub_eff_to_string sub1 in
                             FStar_Util.print1 "Final sub_effect: %s\n"
                               uu____9431
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
          let uu____9468 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9468 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____9471 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____9471
        then tc_layered_lift env sub
        else
          (let uu____9478 =
             let uu____9485 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9485 in
           match uu____9478 with
           | (a, wp_a_src) ->
               let uu____9492 =
                 let uu____9499 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9499 in
               (match uu____9492 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9507 =
                        let uu____9510 =
                          let uu____9511 =
                            let uu____9518 = FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____9518) in
                          FStar_Syntax_Syntax.NT uu____9511 in
                        [uu____9510] in
                      FStar_Syntax_Subst.subst uu____9507 wp_b_tgt in
                    let expected_k =
                      let uu____9526 =
                        let uu____9535 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____9542 =
                          let uu____9551 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____9551] in
                        uu____9535 :: uu____9542 in
                      let uu____9576 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____9526 uu____9576 in
                    let repr_type eff_name a1 wp =
                      (let uu____9598 =
                         let uu____9600 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____9600 in
                       if uu____9598
                       then
                         let uu____9603 =
                           let uu____9609 =
                             let uu____9611 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9611 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9609) in
                         let uu____9615 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____9603 uu____9615
                       else ());
                      (let uu____9618 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____9618 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____9651 =
                               let uu____9652 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____9652
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9651 in
                           let uu____9659 =
                             let uu____9660 =
                               let uu____9677 =
                                 let uu____9688 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____9697 =
                                   let uu____9708 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____9708] in
                                 uu____9688 :: uu____9697 in
                               (repr, uu____9677) in
                             FStar_Syntax_Syntax.Tm_app uu____9660 in
                           let uu____9753 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____9659 uu____9753) in
                    let uu____9754 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____9927 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9938 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____9938 with
                              | (usubst, uvs1) ->
                                  let uu____9961 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____9962 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____9961, uu____9962)
                            else (env, lift_wp) in
                          (match uu____9927 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____10012 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____10012)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____10083 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____10098 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____10098 with
                              | (usubst, uvs) ->
                                  let uu____10123 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____10123)
                            else ([], lift) in
                          (match uu____10083 with
                           | (uvs, lift1) ->
                               ((let uu____10159 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____10159
                                 then
                                   let uu____10163 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10163
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____10169 =
                                   let uu____10176 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10176 lift1 in
                                 match uu____10169 with
                                 | (lift2, comp, uu____10201) ->
                                     let uu____10202 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____10202 with
                                      | (uu____10231, lift_wp, lift_elab) ->
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
                                            let uu____10263 =
                                              let uu____10274 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____10274 in
                                            let uu____10291 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____10263, uu____10291)
                                          else
                                            (let uu____10320 =
                                               let uu____10331 =
                                                 let uu____10340 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____10340) in
                                               FStar_Pervasives_Native.Some
                                                 uu____10331 in
                                             let uu____10355 =
                                               let uu____10364 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____10364) in
                                             (uu____10320, uu____10355)))))) in
                    (match uu____9754 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1084_10428 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1084_10428.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1084_10428.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1084_10428.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1084_10428.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1084_10428.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1084_10428.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1084_10428.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1084_10428.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1084_10428.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1084_10428.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1084_10428.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1084_10428.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1084_10428.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1084_10428.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1084_10428.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1084_10428.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1084_10428.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1084_10428.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1084_10428.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1084_10428.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1084_10428.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1084_10428.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1084_10428.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1084_10428.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1084_10428.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1084_10428.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1084_10428.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1084_10428.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1084_10428.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1084_10428.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1084_10428.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1084_10428.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1084_10428.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1084_10428.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1084_10428.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1084_10428.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1084_10428.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1084_10428.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1084_10428.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1084_10428.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1084_10428.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1084_10428.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1084_10428.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1084_10428.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1084_10428.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1084_10428.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____10461 =
                                 let uu____10466 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____10466 with
                                 | (usubst, uvs1) ->
                                     let uu____10489 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____10490 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____10489, uu____10490) in
                               (match uu____10461 with
                                | (env2, lift2) ->
                                    let uu____10495 =
                                      let uu____10502 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10502 in
                                    (match uu____10495 with
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
                                             let uu____10528 =
                                               let uu____10529 =
                                                 let uu____10546 =
                                                   let uu____10557 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____10566 =
                                                     let uu____10577 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____10577] in
                                                   uu____10557 :: uu____10566 in
                                                 (lift_wp1, uu____10546) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____10529 in
                                             let uu____10622 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____10528 uu____10622 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____10626 =
                                             let uu____10635 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____10642 =
                                               let uu____10651 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____10658 =
                                                 let uu____10667 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____10667] in
                                               uu____10651 :: uu____10658 in
                                             uu____10635 :: uu____10642 in
                                           let uu____10698 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____10626 uu____10698 in
                                         let uu____10701 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____10701 with
                                          | (expected_k2, uu____10711,
                                             uu____10712) ->
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
                                                   let uu____10720 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____10720)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____10728 =
                             let uu____10730 =
                               let uu____10732 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____10732
                                 FStar_List.length in
                             uu____10730 <> Prims.int_one in
                           if uu____10728
                           then
                             let uu____10755 =
                               let uu____10761 =
                                 let uu____10763 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____10765 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____10767 =
                                   let uu____10769 =
                                     let uu____10771 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____10771
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____10769
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10763 uu____10765 uu____10767 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10761) in
                             FStar_Errors.raise_error uu____10755 r
                           else ());
                          (let uu____10798 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10801 =
                                  let uu____10803 =
                                    let uu____10806 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____10806
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____10803
                                    FStar_List.length in
                                uu____10801 <> Prims.int_one) in
                           if uu____10798
                           then
                             let uu____10845 =
                               let uu____10851 =
                                 let uu____10853 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____10855 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____10857 =
                                   let uu____10859 =
                                     let uu____10861 =
                                       let uu____10864 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____10864
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____10861
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____10859
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10853 uu____10855 uu____10857 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10851) in
                             FStar_Errors.raise_error uu____10845 r
                           else ());
                          (let uu___1121_10906 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1121_10906.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1121_10906.FStar_Syntax_Syntax.target);
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
    fun uu____10937 ->
      fun r ->
        match uu____10937 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____10960 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10988 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____10988 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____11019 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____11019 c in
                     let uu____11028 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____11028, uvs1, tps1, c1)) in
            (match uu____10960 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____11048 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____11048 with
                  | (tps2, c2) ->
                      let uu____11063 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____11063 with
                       | (tps3, env3, us) ->
                           let uu____11081 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____11081 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____11107)::uu____11108 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____11127 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____11135 =
                                    let uu____11137 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____11137 in
                                  if uu____11135
                                  then
                                    let uu____11140 =
                                      let uu____11146 =
                                        let uu____11148 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____11150 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11148 uu____11150 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11146) in
                                    FStar_Errors.raise_error uu____11140 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____11158 =
                                    let uu____11159 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11159 in
                                  match uu____11158 with
                                  | (uvs2, t) ->
                                      let uu____11188 =
                                        let uu____11193 =
                                          let uu____11206 =
                                            let uu____11207 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____11207.FStar_Syntax_Syntax.n in
                                          (tps4, uu____11206) in
                                        match uu____11193 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11222, c5)) -> ([], c5)
                                        | (uu____11264,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____11303 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____11188 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11335 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____11335 with
                                               | (uu____11340, t1) ->
                                                   let uu____11342 =
                                                     let uu____11348 =
                                                       let uu____11350 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____11352 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____11356 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11350
                                                         uu____11352
                                                         uu____11356 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11348) in
                                                   FStar_Errors.raise_error
                                                     uu____11342 r)
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
              let uu____11398 =
                let uu____11400 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11400 FStar_Ident.string_of_id in
              let uu____11402 =
                let uu____11404 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11404 FStar_Ident.string_of_id in
              let uu____11406 =
                let uu____11408 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____11408 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11398 uu____11402
                uu____11406 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____11416 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____11416 with
            | (us, t, ty) ->
                let uu____11432 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____11432 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11445 =
                         let uu____11450 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____11450
                           (fun uu____11467 ->
                              match uu____11467 with
                              | (t1, u) ->
                                  let uu____11478 =
                                    let uu____11479 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____11479
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____11478, u)) in
                       match uu____11445 with
                       | (a, u_a) ->
                           let uu____11487 =
                             let uu____11492 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____11492
                               (fun uu____11509 ->
                                  match uu____11509 with
                                  | (t1, u) ->
                                      let uu____11520 =
                                        let uu____11521 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____11521
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____11520, u)) in
                           (match uu____11487 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____11538 =
                                    let uu____11539 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____11539.FStar_Syntax_Syntax.n in
                                  match uu____11538 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____11551) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11579 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____11579 with
                                       | (a', uu____11589)::(b', uu____11591)::bs1
                                           ->
                                           let uu____11621 =
                                             let uu____11622 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____11622
                                               FStar_Pervasives_Native.fst in
                                           let uu____11688 =
                                             let uu____11701 =
                                               let uu____11704 =
                                                 let uu____11705 =
                                                   let uu____11712 =
                                                     let uu____11715 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____11715
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____11712) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11705 in
                                               let uu____11728 =
                                                 let uu____11731 =
                                                   let uu____11732 =
                                                     let uu____11739 =
                                                       let uu____11742 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____11742
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____11739) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11732 in
                                                 [uu____11731] in
                                               uu____11704 :: uu____11728 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11701 in
                                           FStar_All.pipe_right uu____11621
                                             uu____11688)
                                  | uu____11763 ->
                                      let uu____11764 =
                                        let uu____11770 =
                                          let uu____11772 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____11774 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11772 uu____11774 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11770) in
                                      FStar_Errors.raise_error uu____11764 r in
                                let bs = a :: b :: rest_bs in
                                let uu____11807 =
                                  let uu____11818 =
                                    let uu____11823 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____11824 =
                                      let uu____11825 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____11825
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11823 r m u_a uu____11824 in
                                  match uu____11818 with
                                  | (repr, g) ->
                                      let uu____11846 =
                                        let uu____11853 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____11853
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____11846, g) in
                                (match uu____11807 with
                                 | (f, guard_f) ->
                                     let uu____11885 =
                                       let x_a =
                                         let uu____11903 =
                                           let uu____11904 =
                                             let uu____11905 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____11905
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11904 in
                                         FStar_All.pipe_right uu____11903
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____11921 =
                                         let uu____11926 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____11945 =
                                           let uu____11946 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____11946
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11926 r n u_b uu____11945 in
                                       match uu____11921 with
                                       | (repr, g) ->
                                           let uu____11967 =
                                             let uu____11974 =
                                               let uu____11975 =
                                                 let uu____11976 =
                                                   let uu____11979 =
                                                     let uu____11982 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11982 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11979 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11976 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11975 in
                                             FStar_All.pipe_right uu____11974
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____11967, g) in
                                     (match uu____11885 with
                                      | (g, guard_g) ->
                                          let uu____12026 =
                                            let uu____12031 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____12032 =
                                              let uu____12033 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____12033
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____12031 r p u_b uu____12032 in
                                          (match uu____12026 with
                                           | (repr, guard_repr) ->
                                               let uu____12048 =
                                                 let uu____12053 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____12054 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____12053
                                                   repr uu____12054 r in
                                               (match uu____12048 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____12066 =
                                                        let uu____12069 =
                                                          let uu____12070 =
                                                            let uu____12071 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____12071] in
                                                          let uu____12072 =
                                                            let uu____12083 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____12083] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____12070;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____12072;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____12069 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____12066 in
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
                                                     (let uu____12143 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____12143
                                                      then
                                                        let uu____12147 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____12153 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____12147
                                                          uu____12153
                                                      else ());
                                                     (let uu____12163 =
                                                        let uu____12169 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____12169) in
                                                      FStar_Errors.log_issue
                                                        r uu____12163);
                                                     (let uu____12173 =
                                                        let uu____12174 =
                                                          let uu____12177 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1) in
                                                          FStar_All.pipe_right
                                                            uu____12177
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1) in
                                                        (us1, uu____12174) in
                                                      ((us1, t), uu____12173)))))))))))
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
            let uu____12224 =
              let uu____12226 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____12226 FStar_Ident.string_of_id in
            let uu____12228 =
              let uu____12230 =
                let uu____12232 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____12232 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____12230 in
            Prims.op_Hat uu____12224 uu____12228 in
          let uu____12235 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____12235 with
          | (us, t, ty) ->
              let uu____12251 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____12251 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____12264 =
                       let uu____12269 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____12269
                         (fun uu____12286 ->
                            match uu____12286 with
                            | (t1, u) ->
                                let uu____12297 =
                                  let uu____12298 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____12298
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____12297, u)) in
                     match uu____12264 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____12315 =
                             let uu____12316 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____12316.FStar_Syntax_Syntax.n in
                           match uu____12315 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____12328)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____12356 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____12356 with
                                | (a', uu____12366)::bs1 ->
                                    let uu____12386 =
                                      let uu____12387 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____12387
                                        FStar_Pervasives_Native.fst in
                                    let uu____12485 =
                                      let uu____12498 =
                                        let uu____12501 =
                                          let uu____12502 =
                                            let uu____12509 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____12509) in
                                          FStar_Syntax_Syntax.NT uu____12502 in
                                        [uu____12501] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____12498 in
                                    FStar_All.pipe_right uu____12386
                                      uu____12485)
                           | uu____12524 ->
                               let uu____12525 =
                                 let uu____12531 =
                                   let uu____12533 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____12535 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____12533 uu____12535 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____12531) in
                               FStar_Errors.raise_error uu____12525 r in
                         let bs = a :: rest_bs in
                         let uu____12562 =
                           let uu____12573 =
                             let uu____12578 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____12579 =
                               let uu____12580 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____12580
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____12578 r m u uu____12579 in
                           match uu____12573 with
                           | (repr, g) ->
                               let uu____12601 =
                                 let uu____12608 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____12608
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____12601, g) in
                         (match uu____12562 with
                          | (f, guard_f) ->
                              let uu____12640 =
                                let uu____12645 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____12646 =
                                  let uu____12647 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____12647
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____12645 r n u uu____12646 in
                              (match uu____12640 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____12662 =
                                     let uu____12667 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____12668 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____12667 ret_t
                                       uu____12668 r in
                                   (match uu____12662 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____12678 =
                                            let uu____12679 =
                                              let uu____12680 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____12680] in
                                            let uu____12681 =
                                              let uu____12692 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____12692] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____12679;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____12681;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____12678 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____12747 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____12747
                                          then
                                            let uu____12752 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____12752
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
                                             let uu____12762 =
                                               let uu____12763 =
                                                 FStar_All.pipe_right k
                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                      env) in
                                               FStar_All.pipe_right
                                                 uu____12763
                                                 (FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta;
                                                    FStar_TypeChecker_Env.Eager_unfolding]
                                                    env) in
                                             FStar_All.pipe_right uu____12762
                                               (FStar_Syntax_Subst.close_univ_vars
                                                  us1) in
                                           (let uu____12767 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____12767
                                            then
                                              let uu____12772 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____12772
                                            else ());
                                           (let uu____12782 =
                                              let uu____12788 =
                                                FStar_Util.format1
                                                  "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                  combinator_name in
                                              (FStar_Errors.Warning_BleedingEdge_Feature,
                                                uu____12788) in
                                            FStar_Errors.log_issue r
                                              uu____12782);
                                           ((us1, t), (us1, k1)))))))))))