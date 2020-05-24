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
             (FStar_Options.Other "LayeredEffects") in
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
             (FStar_Options.Other "LayeredEffects") in
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
                   (FStar_Options.Other "LayeredEffects") in
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
               let uu____2159 =
                 check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
               match uu____2159 with
               | (stronger_us, stronger_t, stronger_ty) ->
                   ((let uu____2184 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                         (FStar_Options.Other "LayeredEffects") in
                     if uu____2184
                     then
                       let uu____2189 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_t) in
                       let uu____2195 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_ty) in
                       FStar_Util.print2
                         "stronger combinator typechecked with term: %s and type: %s\n"
                         uu____2189 uu____2195
                     else ());
                    (let uu____2204 =
                       FStar_Syntax_Subst.open_univ_vars stronger_us
                         stronger_ty in
                     match uu____2204 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2225 = fresh_a_and_u_a "a" in
                           match uu____2225 with
                           | (a, u) ->
                               let rest_bs =
                                 let uu____2254 =
                                   let uu____2255 =
                                     FStar_Syntax_Subst.compress ty in
                                   uu____2255.FStar_Syntax_Syntax.n in
                                 match uu____2254 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs, uu____2267) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____2295 =
                                       FStar_Syntax_Subst.open_binders bs in
                                     (match uu____2295 with
                                      | (a', uu____2305)::bs1 ->
                                          let uu____2325 =
                                            let uu____2326 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one)) in
                                            FStar_All.pipe_right uu____2326
                                              FStar_Pervasives_Native.fst in
                                          let uu____2424 =
                                            let uu____2437 =
                                              let uu____2440 =
                                                let uu____2441 =
                                                  let uu____2448 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a) in
                                                  (a', uu____2448) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____2441 in
                                              [uu____2440] in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____2437 in
                                          FStar_All.pipe_right uu____2325
                                            uu____2424)
                                 | uu____2463 ->
                                     not_an_arrow_error "stronger"
                                       (Prims.of_int (2)) ty r in
                               let bs = a :: rest_bs in
                               let uu____2481 =
                                 let uu____2492 =
                                   let uu____2497 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs in
                                   let uu____2498 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name in
                                   fresh_repr r uu____2497 u uu____2498 in
                                 match uu____2492 with
                                 | (repr1, g) ->
                                     let uu____2513 =
                                       let uu____2520 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1 in
                                       FStar_All.pipe_right uu____2520
                                         FStar_Syntax_Syntax.mk_binder in
                                     (uu____2513, g) in
                               (match uu____2481 with
                                | (f, guard_f) ->
                                    let uu____2560 =
                                      let uu____2565 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____2566 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____2565 u uu____2566 in
                                    (match uu____2560 with
                                     | (ret_t, guard_ret_t) ->
                                         let uu____2583 =
                                           let uu____2588 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs in
                                           let uu____2589 =
                                             let uu____2591 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             FStar_Util.format1
                                               "implicit for pure_wp in checking stronger for %s"
                                               uu____2591 in
                                           pure_wp_uvar uu____2588 ret_t
                                             uu____2589 r in
                                         (match uu____2583 with
                                          | (pure_wp_uvar1, guard_wp) ->
                                              let c =
                                                let uu____2609 =
                                                  let uu____2610 =
                                                    let uu____2611 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        () in
                                                    [uu____2611] in
                                                  let uu____2612 =
                                                    let uu____2623 =
                                                      FStar_All.pipe_right
                                                        pure_wp_uvar1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____2623] in
                                                  {
                                                    FStar_Syntax_Syntax.comp_univs
                                                      = uu____2610;
                                                    FStar_Syntax_Syntax.effect_name
                                                      =
                                                      FStar_Parser_Const.effect_PURE_lid;
                                                    FStar_Syntax_Syntax.result_typ
                                                      = ret_t;
                                                    FStar_Syntax_Syntax.effect_args
                                                      = uu____2612;
                                                    FStar_Syntax_Syntax.flags
                                                      = []
                                                  } in
                                                FStar_Syntax_Syntax.mk_Comp
                                                  uu____2609 in
                                              let k =
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs [f])
                                                  c in
                                              ((let uu____2678 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "LayeredEffects") in
                                                if uu____2678
                                                then
                                                  let uu____2683 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected type before unification: %s\n"
                                                    uu____2683
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
                                                (let uu____2690 =
                                                   let uu____2693 =
                                                     let uu____2694 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____2694
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   FStar_All.pipe_right
                                                     uu____2693
                                                     (FStar_Syntax_Subst.close_univ_vars
                                                        stronger_us) in
                                                 (stronger_us, stronger_t,
                                                   uu____2690))))))))))) in
             log_combinator "stronger_repr" stronger_repr;
             (let if_then_else =
                let if_then_else_ts =
                  let uu____2723 =
                    FStar_All.pipe_right ed
                      FStar_Syntax_Util.get_layered_if_then_else_combinator in
                  FStar_All.pipe_right uu____2723 FStar_Util.must in
                let r =
                  (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                let uu____2735 =
                  check_and_gen1 "if_then_else" Prims.int_one if_then_else_ts in
                match uu____2735 with
                | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                    let uu____2759 =
                      FStar_Syntax_Subst.open_univ_vars if_then_else_us
                        if_then_else_t in
                    (match uu____2759 with
                     | (us, t) ->
                         let uu____2778 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_ty in
                         (match uu____2778 with
                          | (uu____2795, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 t (FStar_Pervasives_Native.Some ty);
                               (let uu____2799 = fresh_a_and_u_a "a" in
                                match uu____2799 with
                                | (a, u_a) ->
                                    let rest_bs =
                                      let uu____2828 =
                                        let uu____2829 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____2829.FStar_Syntax_Syntax.n in
                                      match uu____2828 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____2841) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____2869 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____2869 with
                                           | (a', uu____2879)::bs1 ->
                                               let uu____2899 =
                                                 let uu____2900 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____2900
                                                   FStar_Pervasives_Native.fst in
                                               let uu____2966 =
                                                 let uu____2979 =
                                                   let uu____2982 =
                                                     let uu____2983 =
                                                       let uu____2990 =
                                                         let uu____2993 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____2993
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       (a', uu____2990) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2983 in
                                                   [uu____2982] in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2979 in
                                               FStar_All.pipe_right
                                                 uu____2899 uu____2966)
                                      | uu____3014 ->
                                          not_an_arrow_error "if_then_else"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: rest_bs in
                                    let uu____3032 =
                                      let uu____3043 =
                                        let uu____3048 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____3049 =
                                          let uu____3050 =
                                            FStar_All.pipe_right a
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____3050
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____3048 u_a
                                          uu____3049 in
                                      match uu____3043 with
                                      | (repr1, g) ->
                                          let uu____3071 =
                                            let uu____3078 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____3078
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____3071, g) in
                                    (match uu____3032 with
                                     | (f_bs, guard_f) ->
                                         let uu____3118 =
                                           let uu____3129 =
                                             let uu____3134 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3135 =
                                               let uu____3136 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst in
                                               FStar_All.pipe_right
                                                 uu____3136
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____3134 u_a
                                               uu____3135 in
                                           match uu____3129 with
                                           | (repr1, g) ->
                                               let uu____3157 =
                                                 let uu____3164 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____3164
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____3157, g) in
                                         (match uu____3118 with
                                          | (g_bs, guard_g) ->
                                              let p_b =
                                                let uu____3211 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "p"
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Util.ktype0 in
                                                FStar_All.pipe_right
                                                  uu____3211
                                                  FStar_Syntax_Syntax.mk_binder in
                                              let uu____3219 =
                                                let uu____3224 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [p_b]) in
                                                let uu____3243 =
                                                  let uu____3244 =
                                                    FStar_All.pipe_right a
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_All.pipe_right
                                                    uu____3244
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____3224 u_a
                                                  uu____3243 in
                                              (match uu____3219 with
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
                                                    (let uu____3304 =
                                                       let uu____3307 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env) in
                                                       FStar_All.pipe_right
                                                         uu____3307
                                                         (FStar_Syntax_Subst.close_univ_vars
                                                            if_then_else_us) in
                                                     (if_then_else_us,
                                                       uu____3304,
                                                       if_then_else_ty)))))))))) in
              log_combinator "if_then_else" if_then_else;
              (let r =
                 let uu____3320 =
                   let uu____3323 =
                     let uu____3332 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_layered_if_then_else_combinator in
                     FStar_All.pipe_right uu____3332 FStar_Util.must in
                   FStar_All.pipe_right uu____3323
                     FStar_Pervasives_Native.snd in
                 uu____3320.FStar_Syntax_Syntax.pos in
               let uu____3361 = if_then_else in
               match uu____3361 with
               | (ite_us, ite_t, uu____3376) ->
                   let uu____3389 =
                     FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                   (match uu____3389 with
                    | (us, ite_t1) ->
                        let uu____3396 =
                          let uu____3411 =
                            let uu____3412 =
                              FStar_Syntax_Subst.compress ite_t1 in
                            uu____3412.FStar_Syntax_Syntax.n in
                          match uu____3411 with
                          | FStar_Syntax_Syntax.Tm_abs
                              (bs, uu____3430, uu____3431) ->
                              let bs1 = FStar_Syntax_Subst.open_binders bs in
                              let uu____3457 =
                                let uu____3470 =
                                  let uu____3475 =
                                    let uu____3478 =
                                      let uu____3487 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                (Prims.of_int (3)))) in
                                      FStar_All.pipe_right uu____3487
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____3478
                                      (FStar_List.map
                                         FStar_Pervasives_Native.fst) in
                                  FStar_All.pipe_right uu____3475
                                    (FStar_List.map
                                       FStar_Syntax_Syntax.bv_to_name) in
                                FStar_All.pipe_right uu____3470
                                  (fun l ->
                                     let uu____3643 = l in
                                     match uu____3643 with
                                     | f::g::p::[] -> (f, g, p)) in
                              (match uu____3457 with
                               | (f, g, p) ->
                                   let uu____3712 =
                                     let uu____3713 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     FStar_TypeChecker_Env.push_binders
                                       uu____3713 bs1 in
                                   let uu____3714 =
                                     let uu____3715 =
                                       let uu____3716 =
                                         let uu____3719 =
                                           FStar_All.pipe_right bs1
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_All.pipe_right uu____3719
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.bv_to_name) in
                                       FStar_All.pipe_right uu____3716
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                       uu____3715 r in
                                   (uu____3712, uu____3714, f, g, p))
                          | uu____3750 ->
                              failwith
                                "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                        (match uu____3396 with
                         | (env, ite_t_applied, f_t, g_t, p_t) ->
                             let uu____3779 =
                               let uu____3788 = stronger_repr in
                               match uu____3788 with
                               | (uu____3809, subcomp_t, subcomp_ty) ->
                                   let uu____3824 =
                                     FStar_Syntax_Subst.open_univ_vars us
                                       subcomp_t in
                                   (match uu____3824 with
                                    | (uu____3837, subcomp_t1) ->
                                        let uu____3839 =
                                          let uu____3850 =
                                            FStar_Syntax_Subst.open_univ_vars
                                              us subcomp_ty in
                                          match uu____3850 with
                                          | (uu____3865, subcomp_ty1) ->
                                              let uu____3867 =
                                                let uu____3868 =
                                                  FStar_Syntax_Subst.compress
                                                    subcomp_ty1 in
                                                uu____3868.FStar_Syntax_Syntax.n in
                                              (match uu____3867 with
                                               | FStar_Syntax_Syntax.Tm_arrow
                                                   (bs, uu____3882) ->
                                                   let uu____3903 =
                                                     FStar_All.pipe_right bs
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs)
                                                             - Prims.int_one)) in
                                                   (match uu____3903 with
                                                    | (bs_except_last,
                                                       last_b) ->
                                                        let uu____4009 =
                                                          FStar_All.pipe_right
                                                            bs_except_last
                                                            (FStar_List.map
                                                               FStar_Pervasives_Native.snd) in
                                                        let uu____4036 =
                                                          let uu____4039 =
                                                            FStar_All.pipe_right
                                                              last_b
                                                              FStar_List.hd in
                                                          FStar_All.pipe_right
                                                            uu____4039
                                                            FStar_Pervasives_Native.snd in
                                                        (uu____4009,
                                                          uu____4036))
                                               | uu____4082 ->
                                                   failwith
                                                     "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                        (match uu____3839 with
                                         | (aqs_except_last, last_aq) ->
                                             let aux t =
                                               let tun_args =
                                                 FStar_All.pipe_right
                                                   aqs_except_last
                                                   (FStar_List.map
                                                      (fun aq ->
                                                         (FStar_Syntax_Syntax.tun,
                                                           aq))) in
                                               FStar_Syntax_Syntax.mk_Tm_app
                                                 subcomp_t1
                                                 (FStar_List.append tun_args
                                                    [(t, last_aq)]) r in
                                             let uu____4193 = aux f_t in
                                             let uu____4196 = aux g_t in
                                             (uu____4193, uu____4196))) in
                             (match uu____3779 with
                              | (subcomp_f, subcomp_g) ->
                                  let uu____4213 =
                                    let aux t =
                                      let uu____4230 =
                                        let uu____4231 =
                                          let uu____4258 =
                                            let uu____4275 =
                                              let uu____4284 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  ite_t_applied in
                                              FStar_Util.Inr uu____4284 in
                                            (uu____4275,
                                              FStar_Pervasives_Native.None) in
                                          (t, uu____4258,
                                            FStar_Pervasives_Native.None) in
                                        FStar_Syntax_Syntax.Tm_ascribed
                                          uu____4231 in
                                      FStar_Syntax_Syntax.mk uu____4230 r in
                                    let uu____4325 = aux subcomp_f in
                                    let uu____4326 = aux subcomp_g in
                                    (uu____4325, uu____4326) in
                                  (match uu____4213 with
                                   | (tm_subcomp_ascribed_f,
                                      tm_subcomp_ascribed_g) ->
                                       ((let uu____4330 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffects") in
                                         if uu____4330
                                         then
                                           let uu____4335 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_f in
                                           let uu____4337 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_g in
                                           FStar_Util.print2
                                             "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                             uu____4335 uu____4337
                                         else ());
                                        (let uu____4342 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env tm_subcomp_ascribed_f in
                                         match uu____4342 with
                                         | (uu____4349, uu____4350, g_f) ->
                                             let g_f1 =
                                               let uu____4353 =
                                                 FStar_TypeChecker_Env.guard_of_guard_formula
                                                   (FStar_TypeChecker_Common.NonTrivial
                                                      p_t) in
                                               FStar_TypeChecker_Env.imp_guard
                                                 uu____4353 g_f in
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env g_f1;
                                              (let uu____4355 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env tm_subcomp_ascribed_g in
                                               match uu____4355 with
                                               | (uu____4362, uu____4363,
                                                  g_g) ->
                                                   let g_g1 =
                                                     let not_p =
                                                       let uu____4367 =
                                                         let uu____4368 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             FStar_Parser_Const.not_lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             FStar_Pervasives_Native.None in
                                                         FStar_All.pipe_right
                                                           uu____4368
                                                           FStar_Syntax_Syntax.fv_to_tm in
                                                       let uu____4369 =
                                                         let uu____4370 =
                                                           FStar_All.pipe_right
                                                             p_t
                                                             FStar_Syntax_Syntax.as_arg in
                                                         [uu____4370] in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____4367
                                                         uu____4369 r in
                                                     let uu____4403 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         (FStar_TypeChecker_Common.NonTrivial
                                                            not_p) in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____4403 g_g in
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
                   (let uu____4427 =
                      let uu____4433 =
                        let uu____4435 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____4437 =
                          FStar_Ident.string_of_lid
                            act.FStar_Syntax_Syntax.action_name in
                        let uu____4439 =
                          FStar_Syntax_Print.binders_to_string "; "
                            act.FStar_Syntax_Syntax.action_params in
                        FStar_Util.format3
                          "Action %s:%s has non-empty action params (%s)"
                          uu____4435 uu____4437 uu____4439 in
                      (FStar_Errors.Fatal_MalformedActionDeclaration,
                        uu____4433) in
                    FStar_Errors.raise_error uu____4427 r)
                 else ();
                 (let uu____4446 =
                    let uu____4451 =
                      FStar_Syntax_Subst.univ_var_opening
                        act.FStar_Syntax_Syntax.action_univs in
                    match uu____4451 with
                    | (usubst, us) ->
                        let uu____4474 =
                          FStar_TypeChecker_Env.push_univ_vars env us in
                        let uu____4475 =
                          let uu___435_4476 = act in
                          let uu____4477 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_defn in
                          let uu____4478 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_typ in
                          {
                            FStar_Syntax_Syntax.action_name =
                              (uu___435_4476.FStar_Syntax_Syntax.action_name);
                            FStar_Syntax_Syntax.action_unqualified_name =
                              (uu___435_4476.FStar_Syntax_Syntax.action_unqualified_name);
                            FStar_Syntax_Syntax.action_univs = us;
                            FStar_Syntax_Syntax.action_params =
                              (uu___435_4476.FStar_Syntax_Syntax.action_params);
                            FStar_Syntax_Syntax.action_defn = uu____4477;
                            FStar_Syntax_Syntax.action_typ = uu____4478
                          } in
                        (uu____4474, uu____4475) in
                  match uu____4446 with
                  | (env1, act1) ->
                      let act_typ =
                        let uu____4482 =
                          let uu____4483 =
                            FStar_Syntax_Subst.compress
                              act1.FStar_Syntax_Syntax.action_typ in
                          uu____4483.FStar_Syntax_Syntax.n in
                        match uu____4482 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                            let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                            let uu____4509 =
                              FStar_Ident.lid_equals
                                ct.FStar_Syntax_Syntax.effect_name
                                ed.FStar_Syntax_Syntax.mname in
                            if uu____4509
                            then
                              let repr_ts =
                                let uu____4513 = repr in
                                match uu____4513 with
                                | (us, t, uu____4528) -> (us, t) in
                              let repr1 =
                                let uu____4546 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts ct.FStar_Syntax_Syntax.comp_univs in
                                FStar_All.pipe_right uu____4546
                                  FStar_Pervasives_Native.snd in
                              let repr2 =
                                let uu____4556 =
                                  let uu____4557 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ in
                                  uu____4557 ::
                                    (ct.FStar_Syntax_Syntax.effect_args) in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____4556 r in
                              let c1 =
                                let uu____4575 =
                                  let uu____4578 =
                                    FStar_TypeChecker_Env.new_u_univ () in
                                  FStar_Pervasives_Native.Some uu____4578 in
                                FStar_Syntax_Syntax.mk_Total' repr2
                                  uu____4575 in
                              FStar_Syntax_Util.arrow bs c1
                            else act1.FStar_Syntax_Syntax.action_typ
                        | uu____4581 -> act1.FStar_Syntax_Syntax.action_typ in
                      let uu____4582 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          act_typ in
                      (match uu____4582 with
                       | (act_typ1, uu____4590, g_t) ->
                           let uu____4592 =
                             let uu____4599 =
                               let uu___460_4600 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   act_typ1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___460_4600.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___460_4600.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___460_4600.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___460_4600.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___460_4600.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___460_4600.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___460_4600.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___460_4600.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___460_4600.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___460_4600.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   false;
                                 FStar_TypeChecker_Env.effects =
                                   (uu___460_4600.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___460_4600.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___460_4600.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___460_4600.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___460_4600.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___460_4600.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___460_4600.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___460_4600.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___460_4600.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___460_4600.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___460_4600.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___460_4600.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___460_4600.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___460_4600.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___460_4600.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___460_4600.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___460_4600.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___460_4600.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___460_4600.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___460_4600.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___460_4600.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___460_4600.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___460_4600.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___460_4600.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___460_4600.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___460_4600.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___460_4600.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___460_4600.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___460_4600.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___460_4600.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___460_4600.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___460_4600.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___460_4600.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___460_4600.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___460_4600.FStar_TypeChecker_Env.erasable_types_tab);
                                 FStar_TypeChecker_Env.enable_defer_to_tac =
                                   (uu___460_4600.FStar_TypeChecker_Env.enable_defer_to_tac)
                               } in
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu____4599
                               act1.FStar_Syntax_Syntax.action_defn in
                           (match uu____4592 with
                            | (act_defn, uu____4603, g_d) ->
                                ((let uu____4606 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "LayeredEffects") in
                                  if uu____4606
                                  then
                                    let uu____4611 =
                                      FStar_Syntax_Print.term_to_string
                                        act_defn in
                                    let uu____4613 =
                                      FStar_Syntax_Print.term_to_string
                                        act_typ1 in
                                    FStar_Util.print2
                                      "Typechecked action definition: %s and action type: %s\n"
                                      uu____4611 uu____4613
                                  else ());
                                 (let uu____4618 =
                                    let act_typ2 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        act_typ1 in
                                    let uu____4626 =
                                      let uu____4627 =
                                        FStar_Syntax_Subst.compress act_typ2 in
                                      uu____4627.FStar_Syntax_Syntax.n in
                                    match uu____4626 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____4637) ->
                                        let bs1 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        let env2 =
                                          FStar_TypeChecker_Env.push_binders
                                            env1 bs1 in
                                        let uu____4660 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____4660 with
                                         | (t, u) ->
                                             let reason =
                                               let uu____4675 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____4677 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               FStar_Util.format2
                                                 "implicit for return type of action %s:%s"
                                                 uu____4675 uu____4677 in
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
                                          let uu____4750 =
                                            let uu____4752 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____4754 =
                                              FStar_Ident.string_of_lid
                                                act1.FStar_Syntax_Syntax.action_name in
                                            let uu____4756 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.format3
                                              "Unexpected non-function type for action %s:%s (%s)"
                                              uu____4752 uu____4754
                                              uu____4756 in
                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                            uu____4750) in
                                        FStar_Errors.raise_error uu____4744 r in
                                  match uu____4618 with
                                  | (k, g_k) ->
                                      ((let uu____4773 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffects") in
                                        if uu____4773
                                        then
                                          let uu____4778 =
                                            FStar_Syntax_Print.term_to_string
                                              k in
                                          FStar_Util.print1
                                            "Expected action type: %s\n"
                                            uu____4778
                                        else ());
                                       (let g =
                                          FStar_TypeChecker_Rel.teq env1
                                            act_typ1 k in
                                        FStar_List.iter
                                          (FStar_TypeChecker_Rel.force_trivial_guard
                                             env1) [g_t; g_d; g_k; g];
                                        (let uu____4786 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffects") in
                                         if uu____4786
                                         then
                                           let uu____4791 =
                                             FStar_Syntax_Print.term_to_string
                                               k in
                                           FStar_Util.print1
                                             "Expected action type after unification: %s\n"
                                             uu____4791
                                         else ());
                                        (let act_typ2 =
                                           let err_msg t =
                                             let uu____4804 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             let uu____4806 =
                                               FStar_Ident.string_of_lid
                                                 act1.FStar_Syntax_Syntax.action_name in
                                             let uu____4808 =
                                               FStar_Syntax_Print.term_to_string
                                                 t in
                                             FStar_Util.format3
                                               "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                               uu____4804 uu____4806
                                               uu____4808 in
                                           let repr_args t =
                                             let uu____4829 =
                                               let uu____4830 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____4830.FStar_Syntax_Syntax.n in
                                             match uu____4829 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (head, a::is) ->
                                                 let uu____4882 =
                                                   let uu____4883 =
                                                     FStar_Syntax_Subst.compress
                                                       head in
                                                   uu____4883.FStar_Syntax_Syntax.n in
                                                 (match uu____4882 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      (uu____4892, us) ->
                                                      (us,
                                                        (FStar_Pervasives_Native.fst
                                                           a), is)
                                                  | uu____4902 ->
                                                      let uu____4903 =
                                                        let uu____4909 =
                                                          err_msg t in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4909) in
                                                      FStar_Errors.raise_error
                                                        uu____4903 r)
                                             | uu____4918 ->
                                                 let uu____4919 =
                                                   let uu____4925 = err_msg t in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____4925) in
                                                 FStar_Errors.raise_error
                                                   uu____4919 r in
                                           let k1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 k in
                                           let uu____4935 =
                                             let uu____4936 =
                                               FStar_Syntax_Subst.compress k1 in
                                             uu____4936.FStar_Syntax_Syntax.n in
                                           match uu____4935 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, c) ->
                                               let uu____4961 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs c in
                                               (match uu____4961 with
                                                | (bs1, c1) ->
                                                    let uu____4968 =
                                                      repr_args
                                                        (FStar_Syntax_Util.comp_result
                                                           c1) in
                                                    (match uu____4968 with
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
                                                         let uu____4979 =
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             ct in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____4979))
                                           | uu____4982 ->
                                               let uu____4983 =
                                                 let uu____4989 = err_msg k1 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____4989) in
                                               FStar_Errors.raise_error
                                                 uu____4983 r in
                                         (let uu____4993 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffects") in
                                          if uu____4993
                                          then
                                            let uu____4998 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.print1
                                              "Action type after injecting it into the monad: %s\n"
                                              uu____4998
                                          else ());
                                         (let act2 =
                                            let uu____5004 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env1 act_defn in
                                            match uu____5004 with
                                            | (us, act_defn1) ->
                                                if
                                                  act1.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then
                                                  let uu___533_5018 = act1 in
                                                  let uu____5019 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      us act_typ2 in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___533_5018.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___533_5018.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      = us;
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___533_5018.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____5019
                                                  }
                                                else
                                                  (let uu____5022 =
                                                     ((FStar_List.length us)
                                                        =
                                                        (FStar_List.length
                                                           act1.FStar_Syntax_Syntax.action_univs))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1 ->
                                                             fun u2 ->
                                                               let uu____5029
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2 in
                                                               uu____5029 =
                                                                 Prims.int_zero)
                                                          us
                                                          act1.FStar_Syntax_Syntax.action_univs) in
                                                   if uu____5022
                                                   then
                                                     let uu___538_5034 = act1 in
                                                     let uu____5035 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                         act_typ2 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___538_5034.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___538_5034.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         =
                                                         (uu___538_5034.FStar_Syntax_Syntax.action_univs);
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___538_5034.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = act_defn1;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____5035
                                                     }
                                                   else
                                                     (let uu____5038 =
                                                        let uu____5044 =
                                                          let uu____5046 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname in
                                                          let uu____5048 =
                                                            FStar_Ident.string_of_lid
                                                              act1.FStar_Syntax_Syntax.action_name in
                                                          let uu____5050 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              us in
                                                          let uu____5052 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              act1.FStar_Syntax_Syntax.action_univs in
                                                          FStar_Util.format4
                                                            "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                            uu____5046
                                                            uu____5048
                                                            uu____5050
                                                            uu____5052 in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____5044) in
                                                      FStar_Errors.raise_error
                                                        uu____5038 r)) in
                                          act2))))))))) in
               let tschemes_of uu____5077 =
                 match uu____5077 with | (us, t, ty) -> ((us, t), (us, ty)) in
               let combinators =
                 let uu____5122 =
                   let uu____5123 = tschemes_of repr in
                   let uu____5128 = tschemes_of return_repr in
                   let uu____5133 = tschemes_of bind_repr in
                   let uu____5138 = tschemes_of stronger_repr in
                   let uu____5143 = tschemes_of if_then_else in
                   {
                     FStar_Syntax_Syntax.l_repr = uu____5123;
                     FStar_Syntax_Syntax.l_return = uu____5128;
                     FStar_Syntax_Syntax.l_bind = uu____5133;
                     FStar_Syntax_Syntax.l_subcomp = uu____5138;
                     FStar_Syntax_Syntax.l_if_then_else = uu____5143
                   } in
                 FStar_Syntax_Syntax.Layered_eff uu____5122 in
               let uu___547_5148 = ed in
               let uu____5149 =
                 FStar_List.map (tc_action env0)
                   ed.FStar_Syntax_Syntax.actions in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___547_5148.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___547_5148.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs =
                   (uu___547_5148.FStar_Syntax_Syntax.univs);
                 FStar_Syntax_Syntax.binders =
                   (uu___547_5148.FStar_Syntax_Syntax.binders);
                 FStar_Syntax_Syntax.signature =
                   (let uu____5156 = signature in
                    match uu____5156 with | (us, t, uu____5171) -> (us, t));
                 FStar_Syntax_Syntax.combinators = combinators;
                 FStar_Syntax_Syntax.actions = uu____5149;
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___547_5148.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5209 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED") in
         if uu____5209
         then
           let uu____5214 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5214
         else ());
        (let uu____5220 =
           let uu____5225 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
           match uu____5225 with
           | (ed_univs_subst, ed_univs) ->
               let bs =
                 let uu____5249 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders in
                 FStar_Syntax_Subst.open_binders uu____5249 in
               let uu____5250 =
                 let uu____5257 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5257 bs in
               (match uu____5250 with
                | (bs1, uu____5263, uu____5264) ->
                    let uu____5265 =
                      let tmp_t =
                        let uu____5275 =
                          let uu____5278 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____5283 ->
                                 FStar_Pervasives_Native.Some uu____5283) in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5278 in
                        FStar_Syntax_Util.arrow bs1 uu____5275 in
                      let uu____5284 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t in
                      match uu____5284 with
                      | (us, tmp_t1) ->
                          let uu____5301 =
                            let uu____5302 =
                              let uu____5303 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals in
                              FStar_All.pipe_right uu____5303
                                FStar_Pervasives_Native.fst in
                            FStar_All.pipe_right uu____5302
                              FStar_Syntax_Subst.close_binders in
                          (us, uu____5301) in
                    (match uu____5265 with
                     | (us, bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5340 ->
                              let uu____5343 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1 ->
                                        fun u2 ->
                                          let uu____5350 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2 in
                                          uu____5350 = Prims.int_zero)
                                     ed_univs us) in
                              if uu____5343
                              then (us, bs2)
                              else
                                (let uu____5361 =
                                   let uu____5367 =
                                     let uu____5369 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname in
                                     let uu____5371 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs) in
                                     let uu____5373 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us) in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____5369 uu____5371 uu____5373 in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5367) in
                                 let uu____5377 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Errors.raise_error uu____5361
                                   uu____5377)))) in
         match uu____5220 with
         | (us, bs) ->
             let ed1 =
               let uu___581_5385 = ed in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___581_5385.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___581_5385.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___581_5385.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___581_5385.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___581_5385.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___581_5385.FStar_Syntax_Syntax.eff_attrs)
               } in
             let uu____5386 = FStar_Syntax_Subst.univ_var_opening us in
             (match uu____5386 with
              | (ed_univs_subst, ed_univs) ->
                  let uu____5405 =
                    let uu____5410 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                    FStar_Syntax_Subst.open_binders' uu____5410 in
                  (match uu____5405 with
                   | (ed_bs, ed_bs_subst) ->
                       let ed2 =
                         let op uu____5431 =
                           match uu____5431 with
                           | (us1, t) ->
                               let t1 =
                                 let uu____5451 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst in
                                 FStar_Syntax_Subst.subst uu____5451 t in
                               let uu____5460 =
                                 let uu____5461 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst in
                                 FStar_Syntax_Subst.subst uu____5461 t1 in
                               (us1, uu____5460) in
                         let uu___595_5466 = ed1 in
                         let uu____5467 =
                           op ed1.FStar_Syntax_Syntax.signature in
                         let uu____5468 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators in
                         let uu____5469 =
                           FStar_List.map
                             (fun a ->
                                let uu___598_5477 = a in
                                let uu____5478 =
                                  let uu____5479 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn)) in
                                  FStar_Pervasives_Native.snd uu____5479 in
                                let uu____5490 =
                                  let uu____5491 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ)) in
                                  FStar_Pervasives_Native.snd uu____5491 in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___598_5477.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___598_5477.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___598_5477.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___598_5477.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5478;
                                  FStar_Syntax_Syntax.action_typ = uu____5490
                                }) ed1.FStar_Syntax_Syntax.actions in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___595_5466.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___595_5466.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___595_5466.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___595_5466.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5467;
                           FStar_Syntax_Syntax.combinators = uu____5468;
                           FStar_Syntax_Syntax.actions = uu____5469;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___595_5466.FStar_Syntax_Syntax.eff_attrs)
                         } in
                       ((let uu____5503 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED") in
                         if uu____5503
                         then
                           let uu____5508 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2 in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5508
                         else ());
                        (let env =
                           let uu____5515 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs in
                           FStar_TypeChecker_Env.push_binders uu____5515
                             ed_bs in
                         let check_and_gen' comb n env_opt uu____5550 k =
                           match uu____5550 with
                           | (us1, t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env in
                               let uu____5570 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t in
                               (match uu____5570 with
                                | (us2, t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5579 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2 in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5579 t1 k1
                                      | FStar_Pervasives_Native.None ->
                                          let uu____5580 =
                                            let uu____5587 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5587 t1 in
                                          (match uu____5580 with
                                           | (t2, uu____5589, g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2)) in
                                    let uu____5592 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2 in
                                    (match uu____5592 with
                                     | (g_us, t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____5608 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname in
                                               let uu____5610 =
                                                 FStar_Util.string_of_int n in
                                               let uu____5612 =
                                                 let uu____5614 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length in
                                                 FStar_All.pipe_right
                                                   uu____5614
                                                   FStar_Util.string_of_int in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____5608 comb uu____5610
                                                 uu____5612 in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5629 ->
                                               let uu____5630 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____5637 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____5637 =
                                                             Prims.int_zero)
                                                      us2 g_us) in
                                               if uu____5630
                                               then (g_us, t3)
                                               else
                                                 (let uu____5648 =
                                                    let uu____5654 =
                                                      let uu____5656 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____5658 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2) in
                                                      let uu____5660 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us) in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____5656 comb
                                                        uu____5658 uu____5660 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5654) in
                                                  FStar_Errors.raise_error
                                                    uu____5648
                                                    t3.FStar_Syntax_Syntax.pos))))) in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None in
                         (let uu____5668 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED") in
                          if uu____5668
                          then
                            let uu____5673 =
                              FStar_Syntax_Print.tscheme_to_string signature in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5673
                          else ());
                         (let fresh_a_and_wp uu____5689 =
                            let fail t =
                              let uu____5702 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t in
                              FStar_Errors.raise_error uu____5702
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                            let uu____5718 =
                              FStar_TypeChecker_Env.inst_tscheme signature in
                            match uu____5718 with
                            | (uu____5729, signature1) ->
                                let uu____5731 =
                                  let uu____5732 =
                                    FStar_Syntax_Subst.compress signature1 in
                                  uu____5732.FStar_Syntax_Syntax.n in
                                (match uu____5731 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1, uu____5742) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1 in
                                     (match bs2 with
                                      | (a, uu____5771)::(wp, uu____5773)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5802 -> fail signature1)
                                 | uu____5803 -> fail signature1) in
                          let log_combinator s ts =
                            let uu____5817 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED") in
                            if uu____5817
                            then
                              let uu____5822 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname in
                              let uu____5824 =
                                FStar_Syntax_Print.tscheme_to_string ts in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____5822 s uu____5824
                            else () in
                          let ret_wp =
                            let uu____5830 = fresh_a_and_wp () in
                            match uu____5830 with
                            | (a, wp_sort) ->
                                let k =
                                  let uu____5846 =
                                    let uu____5855 =
                                      FStar_Syntax_Syntax.mk_binder a in
                                    let uu____5862 =
                                      let uu____5871 =
                                        let uu____5878 =
                                          FStar_Syntax_Syntax.bv_to_name a in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5878 in
                                      [uu____5871] in
                                    uu____5855 :: uu____5862 in
                                  let uu____5897 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                  FStar_Syntax_Util.arrow uu____5846
                                    uu____5897 in
                                let uu____5900 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5900
                                  (FStar_Pervasives_Native.Some k) in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5914 = fresh_a_and_wp () in
                             match uu____5914 with
                             | (a, wp_sort_a) ->
                                 let uu____5927 = fresh_a_and_wp () in
                                 (match uu____5927 with
                                  | (b, wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5943 =
                                          let uu____5952 =
                                            let uu____5959 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5959 in
                                          [uu____5952] in
                                        let uu____5972 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____5943
                                          uu____5972 in
                                      let k =
                                        let uu____5978 =
                                          let uu____5987 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____5994 =
                                            let uu____6003 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____6010 =
                                              let uu____6019 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____6026 =
                                                let uu____6035 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a in
                                                let uu____6042 =
                                                  let uu____6051 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b in
                                                  [uu____6051] in
                                                uu____6035 :: uu____6042 in
                                              uu____6019 :: uu____6026 in
                                            uu____6003 :: uu____6010 in
                                          uu____5987 :: uu____5994 in
                                        let uu____6094 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____5978
                                          uu____6094 in
                                      let uu____6097 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6097
                                        (FStar_Pervasives_Native.Some k)) in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6111 = fresh_a_and_wp () in
                              match uu____6111 with
                              | (a, wp_sort_a) ->
                                  let uu____6124 =
                                    FStar_Syntax_Util.type_u () in
                                  (match uu____6124 with
                                   | (t, uu____6130) ->
                                       let k =
                                         let uu____6134 =
                                           let uu____6143 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____6150 =
                                             let uu____6159 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____6166 =
                                               let uu____6175 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____6175] in
                                             uu____6159 :: uu____6166 in
                                           uu____6143 :: uu____6150 in
                                         let uu____6206 =
                                           FStar_Syntax_Syntax.mk_Total t in
                                         FStar_Syntax_Util.arrow uu____6134
                                           uu____6206 in
                                       let uu____6209 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6209
                                         (FStar_Pervasives_Native.Some k)) in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____6223 = fresh_a_and_wp () in
                               match uu____6223 with
                               | (a, wp_sort_a) ->
                                   let p =
                                     let uu____6237 =
                                       let uu____6240 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname in
                                       FStar_Pervasives_Native.Some
                                         uu____6240 in
                                     let uu____6241 =
                                       let uu____6242 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____6242
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.new_bv uu____6237
                                       uu____6241 in
                                   let k =
                                     let uu____6254 =
                                       let uu____6263 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____6270 =
                                         let uu____6279 =
                                           FStar_Syntax_Syntax.mk_binder p in
                                         let uu____6286 =
                                           let uu____6295 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a in
                                           let uu____6302 =
                                             let uu____6311 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             [uu____6311] in
                                           uu____6295 :: uu____6302 in
                                         uu____6279 :: uu____6286 in
                                       uu____6263 :: uu____6270 in
                                     let uu____6348 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a in
                                     FStar_Syntax_Util.arrow uu____6254
                                       uu____6348 in
                                   let uu____6351 =
                                     let uu____6356 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                     FStar_All.pipe_right uu____6356
                                       FStar_Util.must in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6351
                                     (FStar_Pervasives_Native.Some k) in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____6388 = fresh_a_and_wp () in
                                match uu____6388 with
                                | (a, wp_sort_a) ->
                                    let k =
                                      let uu____6404 =
                                        let uu____6413 =
                                          FStar_Syntax_Syntax.mk_binder a in
                                        let uu____6420 =
                                          let uu____6429 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a in
                                          [uu____6429] in
                                        uu____6413 :: uu____6420 in
                                      let uu____6454 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a in
                                      FStar_Syntax_Util.arrow uu____6404
                                        uu____6454 in
                                    let uu____6457 =
                                      let uu____6462 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator in
                                      FStar_All.pipe_right uu____6462
                                        FStar_Util.must in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6457
                                      (FStar_Pervasives_Native.Some k) in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6478 = fresh_a_and_wp () in
                                 match uu____6478 with
                                 | (a, wp_sort_a) ->
                                     let b =
                                       let uu____6492 =
                                         let uu____6495 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____6495 in
                                       let uu____6496 =
                                         let uu____6497 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____6497
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____6492
                                         uu____6496 in
                                     let wp_sort_b_a =
                                       let uu____6509 =
                                         let uu____6518 =
                                           let uu____6525 =
                                             FStar_Syntax_Syntax.bv_to_name b in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6525 in
                                         [uu____6518] in
                                       let uu____6538 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____6509
                                         uu____6538 in
                                     let k =
                                       let uu____6544 =
                                         let uu____6553 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____6560 =
                                           let uu____6569 =
                                             FStar_Syntax_Syntax.mk_binder b in
                                           let uu____6576 =
                                             let uu____6585 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a in
                                             [uu____6585] in
                                           uu____6569 :: uu____6576 in
                                         uu____6553 :: uu____6560 in
                                       let uu____6616 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____6544
                                         uu____6616 in
                                     let uu____6619 =
                                       let uu____6624 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator in
                                       FStar_All.pipe_right uu____6624
                                         FStar_Util.must in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6619
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6640 = fresh_a_and_wp () in
                                  match uu____6640 with
                                  | (a, wp_sort_a) ->
                                      let uu____6653 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____6653 with
                                       | (t, uu____6659) ->
                                           let k =
                                             let uu____6663 =
                                               let uu____6672 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____6679 =
                                                 let uu____6688 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____6688] in
                                               uu____6672 :: uu____6679 in
                                             let uu____6713 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t in
                                             FStar_Syntax_Util.arrow
                                               uu____6663 uu____6713 in
                                           let trivial =
                                             let uu____6717 =
                                               let uu____6722 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator in
                                               FStar_All.pipe_right
                                                 uu____6722 FStar_Util.must in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6717
                                               (FStar_Pervasives_Native.Some
                                                  k) in
                                           (log_combinator "trivial" trivial;
                                            trivial)) in
                                let uu____6737 =
                                  let uu____6754 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr in
                                  match uu____6754 with
                                  | FStar_Pervasives_Native.None ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6783 ->
                                      let repr =
                                        let uu____6787 = fresh_a_and_wp () in
                                        match uu____6787 with
                                        | (a, wp_sort_a) ->
                                            let uu____6800 =
                                              FStar_Syntax_Util.type_u () in
                                            (match uu____6800 with
                                             | (t, uu____6806) ->
                                                 let k =
                                                   let uu____6810 =
                                                     let uu____6819 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a in
                                                     let uu____6826 =
                                                       let uu____6835 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       [uu____6835] in
                                                     uu____6819 :: uu____6826 in
                                                   let uu____6860 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6810 uu____6860 in
                                                 let uu____6863 =
                                                   let uu____6868 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr in
                                                   FStar_All.pipe_right
                                                     uu____6868
                                                     FStar_Util.must in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6863
                                                   (FStar_Pervasives_Native.Some
                                                      k)) in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6912 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr in
                                          match uu____6912 with
                                          | (uu____6919, repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1 in
                                              let uu____6922 =
                                                let uu____6923 =
                                                  let uu____6940 =
                                                    let uu____6951 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____6968 =
                                                      let uu____6979 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____6979] in
                                                    uu____6951 :: uu____6968 in
                                                  (repr2, uu____6940) in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____6923 in
                                              FStar_Syntax_Syntax.mk
                                                uu____6922
                                                FStar_Range.dummyRange in
                                        let mk_repr a wp =
                                          let uu____7045 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          mk_repr' uu____7045 wp in
                                        let destruct_repr t =
                                          let uu____7060 =
                                            let uu____7061 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____7061.FStar_Syntax_Syntax.n in
                                          match uu____7060 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7072,
                                               (t1, uu____7074)::(wp,
                                                                  uu____7076)::[])
                                              -> (t1, wp)
                                          | uu____7135 ->
                                              failwith "Unexpected repr type" in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7151 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr in
                                            FStar_All.pipe_right uu____7151
                                              FStar_Util.must in
                                          let uu____7178 = fresh_a_and_wp () in
                                          match uu____7178 with
                                          | (a, uu____7186) ->
                                              let x_a =
                                                let uu____7192 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7192 in
                                              let res =
                                                let wp =
                                                  let uu____7198 =
                                                    let uu____7199 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp in
                                                    FStar_All.pipe_right
                                                      uu____7199
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____7208 =
                                                    let uu____7209 =
                                                      let uu____7218 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_All.pipe_right
                                                        uu____7218
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____7227 =
                                                      let uu____7238 =
                                                        let uu____7247 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a in
                                                        FStar_All.pipe_right
                                                          uu____7247
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____7238] in
                                                    uu____7209 :: uu____7227 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____7198 uu____7208
                                                    FStar_Range.dummyRange in
                                                mk_repr a wp in
                                              let k =
                                                let uu____7283 =
                                                  let uu____7292 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____7299 =
                                                    let uu____7308 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a in
                                                    [uu____7308] in
                                                  uu____7292 :: uu____7299 in
                                                let uu____7333 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res in
                                                FStar_Syntax_Util.arrow
                                                  uu____7283 uu____7333 in
                                              let uu____7336 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k in
                                              (match uu____7336 with
                                               | (k1, uu____7344, uu____7345)
                                                   ->
                                                   let env1 =
                                                     let uu____7349 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7349 in
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
                                             let uu____7362 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr in
                                             FStar_All.pipe_right uu____7362
                                               FStar_Util.must in
                                           let r =
                                             let uu____7400 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None in
                                             FStar_All.pipe_right uu____7400
                                               FStar_Syntax_Syntax.fv_to_tm in
                                           let uu____7401 = fresh_a_and_wp () in
                                           match uu____7401 with
                                           | (a, wp_sort_a) ->
                                               let uu____7414 =
                                                 fresh_a_and_wp () in
                                               (match uu____7414 with
                                                | (b, wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7430 =
                                                        let uu____7439 =
                                                          let uu____7446 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7446 in
                                                        [uu____7439] in
                                                      let uu____7459 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7430 uu____7459 in
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
                                                      let uu____7467 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7467 in
                                                    let wp_g_x =
                                                      let uu____7470 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g in
                                                      let uu____7471 =
                                                        let uu____7472 =
                                                          let uu____7481 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____7481
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____7472] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____7470 uu____7471
                                                        FStar_Range.dummyRange in
                                                    let res =
                                                      let wp =
                                                        let uu____7510 =
                                                          let uu____7511 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp in
                                                          FStar_All.pipe_right
                                                            uu____7511
                                                            FStar_Pervasives_Native.snd in
                                                        let uu____7520 =
                                                          let uu____7521 =
                                                            let uu____7524 =
                                                              let uu____7527
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a in
                                                              let uu____7528
                                                                =
                                                                let uu____7531
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                let uu____7532
                                                                  =
                                                                  let uu____7535
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  let uu____7536
                                                                    =
                                                                    let uu____7539
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____7539] in
                                                                  uu____7535
                                                                    ::
                                                                    uu____7536 in
                                                                uu____7531 ::
                                                                  uu____7532 in
                                                              uu____7527 ::
                                                                uu____7528 in
                                                            r :: uu____7524 in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____7521 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7510
                                                          uu____7520
                                                          FStar_Range.dummyRange in
                                                      mk_repr b wp in
                                                    let maybe_range_arg =
                                                      let uu____7557 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs in
                                                      if uu____7557
                                                      then
                                                        let uu____7568 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range in
                                                        let uu____7575 =
                                                          let uu____7584 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          [uu____7584] in
                                                        uu____7568 ::
                                                          uu____7575
                                                      else [] in
                                                    let k =
                                                      let uu____7620 =
                                                        let uu____7629 =
                                                          let uu____7638 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a in
                                                          let uu____7645 =
                                                            let uu____7654 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b in
                                                            [uu____7654] in
                                                          uu____7638 ::
                                                            uu____7645 in
                                                        let uu____7679 =
                                                          let uu____7688 =
                                                            let uu____7697 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f in
                                                            let uu____7704 =
                                                              let uu____7713
                                                                =
                                                                let uu____7720
                                                                  =
                                                                  let uu____7721
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  mk_repr a
                                                                    uu____7721 in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7720 in
                                                              let uu____7722
                                                                =
                                                                let uu____7731
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                let uu____7738
                                                                  =
                                                                  let uu____7747
                                                                    =
                                                                    let uu____7754
                                                                    =
                                                                    let uu____7755
                                                                    =
                                                                    let uu____7764
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____7764] in
                                                                    let uu____7783
                                                                    =
                                                                    let uu____7786
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7786 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7755
                                                                    uu____7783 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7754 in
                                                                  [uu____7747] in
                                                                uu____7731 ::
                                                                  uu____7738 in
                                                              uu____7713 ::
                                                                uu____7722 in
                                                            uu____7697 ::
                                                              uu____7704 in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7688 in
                                                        FStar_List.append
                                                          uu____7629
                                                          uu____7679 in
                                                      let uu____7831 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7620 uu____7831 in
                                                    let uu____7834 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k in
                                                    (match uu____7834 with
                                                     | (k1, uu____7842,
                                                        uu____7843) ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___793_7853
                                                                = env1 in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___793_7853.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____7855
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____7855) in
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
                                              (let uu____7882 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7896 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs in
                                                    match uu____7896 with
                                                    | (usubst, uvs) ->
                                                        let uu____7919 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs in
                                                        let uu____7920 =
                                                          let uu___806_7921 =
                                                            act in
                                                          let uu____7922 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn in
                                                          let uu____7923 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___806_7921.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___806_7921.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___806_7921.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7922;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7923
                                                          } in
                                                        (uu____7919,
                                                          uu____7920)) in
                                               match uu____7882 with
                                               | (env1, act1) ->
                                                   let act_typ =
                                                     let uu____7927 =
                                                       let uu____7928 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                       uu____7928.FStar_Syntax_Syntax.n in
                                                     match uu____7927 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1, c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c in
                                                         let uu____7954 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname in
                                                         if uu____7954
                                                         then
                                                           let uu____7957 =
                                                             let uu____7960 =
                                                               let uu____7961
                                                                 =
                                                                 let uu____7962
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7962 in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7961 in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7960 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7957
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7985 ->
                                                         act1.FStar_Syntax_Syntax.action_typ in
                                                   let uu____7986 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ in
                                                   (match uu____7986 with
                                                    | (act_typ1, uu____7994,
                                                       g_t) ->
                                                        let env' =
                                                          let uu___823_7997 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1 in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___823_7997.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          } in
                                                        ((let uu____8000 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED") in
                                                          if uu____8000
                                                          then
                                                            let uu____8004 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____8006 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            let uu____8008 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1 in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8004
                                                              uu____8006
                                                              uu____8008
                                                          else ());
                                                         (let uu____8013 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn in
                                                          match uu____8013
                                                          with
                                                          | (act_defn,
                                                             uu____8021, g_a)
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
                                                              let uu____8025
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
                                                                    let uu____8061
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____8061
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____8073)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____8080
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8080 in
                                                                    let uu____8083
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____8083
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____8097,
                                                                    g) ->
                                                                    (k1, g)))
                                                                | uu____8101
                                                                    ->
                                                                    let uu____8102
                                                                    =
                                                                    let uu____8108
                                                                    =
                                                                    let uu____8110
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____8112
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8110
                                                                    uu____8112 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8108) in
                                                                    FStar_Errors.raise_error
                                                                    uu____8102
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                              (match uu____8025
                                                               with
                                                               | (expected_k,
                                                                  g_k) ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                   ((
                                                                    let uu____8130
                                                                    =
                                                                    let uu____8131
                                                                    =
                                                                    let uu____8132
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8132 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8131 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8130);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8134
                                                                    =
                                                                    let uu____8135
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____8135.FStar_Syntax_Syntax.n in
                                                                    match uu____8134
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____8160
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____8160
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____8167
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____8167
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____8187
                                                                    =
                                                                    let uu____8188
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____8188] in
                                                                    let uu____8189
                                                                    =
                                                                    let uu____8200
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____8200] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8187;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8189;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____8225
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8225))
                                                                    | 
                                                                    uu____8228
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____8230
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8252
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8252)) in
                                                                    match uu____8230
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
                                                                    let uu___873_8271
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___873_8271.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___873_8271.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___873_8271.FStar_Syntax_Syntax.action_params);
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
                                match uu____6737 with
                                | (repr, return_repr, bind_repr, actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs in
                                      let uu____8314 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8314 ts1 in
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
                                          uu____8326 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8327 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8328 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected" in
                                    let ed3 =
                                      let uu___893_8331 = ed2 in
                                      let uu____8332 = cl signature in
                                      let uu____8333 =
                                        FStar_List.map
                                          (fun a ->
                                             let uu___896_8341 = a in
                                             let uu____8342 =
                                               let uu____8343 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn)) in
                                               FStar_All.pipe_right
                                                 uu____8343
                                                 FStar_Pervasives_Native.snd in
                                             let uu____8368 =
                                               let uu____8369 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ)) in
                                               FStar_All.pipe_right
                                                 uu____8369
                                                 FStar_Pervasives_Native.snd in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___896_8341.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___896_8341.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___896_8341.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___896_8341.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8342;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8368
                                             }) actions in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___893_8331.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___893_8331.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___893_8331.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___893_8331.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8332;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8333;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___893_8331.FStar_Syntax_Syntax.eff_attrs)
                                      } in
                                    ((let uu____8395 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED") in
                                      if uu____8395
                                      then
                                        let uu____8400 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8400
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
        let uu____8426 =
          let uu____8441 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
          if uu____8441 then tc_layered_eff_decl else tc_non_layered_eff_decl in
        uu____8426 env ed quals
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
        let fail uu____8491 =
          let uu____8492 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____8498 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____8492 uu____8498 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____8542)::(wp, uu____8544)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8573 -> fail ())
        | uu____8574 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____8587 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects") in
       if uu____8587
       then
         let uu____8592 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8592
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____8617 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____8617.FStar_Syntax_Syntax.pos in
       let uu____8630 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____8630 with
       | (us, lift, lift_ty) ->
           ((let uu____8644 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffects") in
             if uu____8644
             then
               let uu____8649 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____8655 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____8649 uu____8655
             else ());
            (let uu____8664 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____8664 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____8682 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____8684 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____8686 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____8682 uu____8684 s uu____8686 in
                   let uu____8689 =
                     let uu____8696 =
                       let uu____8701 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____8701
                         (fun uu____8718 ->
                            match uu____8718 with
                            | (t, u) ->
                                let uu____8729 =
                                  let uu____8730 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____8730
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____8729, u)) in
                     match uu____8696 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____8749 =
                             let uu____8750 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____8750.FStar_Syntax_Syntax.n in
                           match uu____8749 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____8762)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____8790 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____8790 with
                                | (a', uu____8800)::bs1 ->
                                    let uu____8820 =
                                      let uu____8821 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____8821
                                        FStar_Pervasives_Native.fst in
                                    let uu____8887 =
                                      let uu____8900 =
                                        let uu____8903 =
                                          let uu____8904 =
                                            let uu____8911 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____8911) in
                                          FStar_Syntax_Syntax.NT uu____8904 in
                                        [uu____8903] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____8900 in
                                    FStar_All.pipe_right uu____8820
                                      uu____8887)
                           | uu____8926 ->
                               let uu____8927 =
                                 let uu____8933 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____8933) in
                               FStar_Errors.raise_error uu____8927 r in
                         let uu____8945 =
                           let uu____8956 =
                             let uu____8961 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____8968 =
                               let uu____8969 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____8969
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____8961 r sub.FStar_Syntax_Syntax.source
                               u_a uu____8968 in
                           match uu____8956 with
                           | (f_sort, g) ->
                               let uu____8990 =
                                 let uu____8997 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____8997
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____8990, g) in
                         (match uu____8945 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____9064 =
                                let uu____9069 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____9070 =
                                  let uu____9071 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____9071
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____9069 r sub.FStar_Syntax_Syntax.target
                                  u_a uu____9070 in
                              (match uu____9064 with
                               | (repr, g_repr) ->
                                   let uu____9088 =
                                     let uu____9093 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____9094 =
                                       let uu____9096 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____9098 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____9096 uu____9098 in
                                     pure_wp_uvar uu____9093 repr uu____9094
                                       r in
                                   (match uu____9088 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____9110 =
                                            let uu____9111 =
                                              let uu____9112 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____9112] in
                                            let uu____9113 =
                                              let uu____9124 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____9124] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____9111;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____9113;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____9110 in
                                        let uu____9157 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____9160 =
                                          let uu____9161 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____9161 guard_wp in
                                        (uu____9157, uu____9160)))) in
                   match uu____8689 with
                   | (k, g_k) ->
                       ((let uu____9171 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffects") in
                         if uu____9171
                         then
                           let uu____9176 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____9176
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____9185 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects") in
                          if uu____9185
                          then
                            let uu____9190 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____9190
                          else ());
                         (let sub1 =
                            let uu___985_9196 = sub in
                            let uu____9197 =
                              let uu____9200 =
                                let uu____9201 =
                                  let uu____9204 =
                                    FStar_All.pipe_right k
                                      (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                         env) in
                                  FStar_All.pipe_right uu____9204
                                    (FStar_Syntax_Subst.close_univ_vars us1) in
                                (us1, uu____9201) in
                              FStar_Pervasives_Native.Some uu____9200 in
                            {
                              FStar_Syntax_Syntax.source =
                                (uu___985_9196.FStar_Syntax_Syntax.source);
                              FStar_Syntax_Syntax.target =
                                (uu___985_9196.FStar_Syntax_Syntax.target);
                              FStar_Syntax_Syntax.lift_wp = uu____9197;
                              FStar_Syntax_Syntax.lift =
                                (FStar_Pervasives_Native.Some (us1, lift))
                            } in
                          (let uu____9216 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects") in
                           if uu____9216
                           then
                             let uu____9221 =
                               FStar_Syntax_Print.sub_eff_to_string sub1 in
                             FStar_Util.print1 "Final sub_effect: %s\n"
                               uu____9221
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
          let uu____9258 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9258 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____9261 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____9261
        then tc_layered_lift env sub
        else
          (let uu____9268 =
             let uu____9275 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____9275 in
           match uu____9268 with
           | (a, wp_a_src) ->
               let uu____9282 =
                 let uu____9289 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____9289 in
               (match uu____9282 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9297 =
                        let uu____9300 =
                          let uu____9301 =
                            let uu____9308 = FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____9308) in
                          FStar_Syntax_Syntax.NT uu____9301 in
                        [uu____9300] in
                      FStar_Syntax_Subst.subst uu____9297 wp_b_tgt in
                    let expected_k =
                      let uu____9316 =
                        let uu____9325 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____9332 =
                          let uu____9341 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____9341] in
                        uu____9325 :: uu____9332 in
                      let uu____9366 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____9316 uu____9366 in
                    let repr_type eff_name a1 wp =
                      (let uu____9388 =
                         let uu____9390 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____9390 in
                       if uu____9388
                       then
                         let uu____9393 =
                           let uu____9399 =
                             let uu____9401 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____9401 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9399) in
                         let uu____9405 = FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____9393 uu____9405
                       else ());
                      (let uu____9408 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____9408 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____9441 =
                               let uu____9442 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____9442
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9441 in
                           let uu____9449 =
                             let uu____9450 =
                               let uu____9467 =
                                 let uu____9478 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____9487 =
                                   let uu____9498 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____9498] in
                                 uu____9478 :: uu____9487 in
                               (repr, uu____9467) in
                             FStar_Syntax_Syntax.Tm_app uu____9450 in
                           let uu____9543 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____9449 uu____9543) in
                    let uu____9544 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____9717 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9728 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____9728 with
                              | (usubst, uvs1) ->
                                  let uu____9751 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____9752 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____9751, uu____9752)
                            else (env, lift_wp) in
                          (match uu____9717 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____9802 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____9802)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____9873 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9888 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____9888 with
                              | (usubst, uvs) ->
                                  let uu____9913 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____9913)
                            else ([], lift) in
                          (match uu____9873 with
                           | (uvs, lift1) ->
                               ((let uu____9949 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____9949
                                 then
                                   let uu____9953 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9953
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____9959 =
                                   let uu____9966 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9966 lift1 in
                                 match uu____9959 with
                                 | (lift2, comp, uu____9991) ->
                                     let uu____9992 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____9992 with
                                      | (uu____10021, lift_wp, lift_elab) ->
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
                                            let uu____10053 =
                                              let uu____10064 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____10064 in
                                            let uu____10081 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____10053, uu____10081)
                                          else
                                            (let uu____10110 =
                                               let uu____10121 =
                                                 let uu____10130 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____10130) in
                                               FStar_Pervasives_Native.Some
                                                 uu____10121 in
                                             let uu____10145 =
                                               let uu____10154 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____10154) in
                                             (uu____10110, uu____10145)))))) in
                    (match uu____9544 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1069_10218 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1069_10218.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1069_10218.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1069_10218.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1069_10218.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1069_10218.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1069_10218.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1069_10218.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1069_10218.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1069_10218.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1069_10218.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1069_10218.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1069_10218.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1069_10218.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1069_10218.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1069_10218.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1069_10218.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1069_10218.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1069_10218.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1069_10218.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1069_10218.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1069_10218.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1069_10218.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1069_10218.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1069_10218.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1069_10218.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1069_10218.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1069_10218.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1069_10218.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1069_10218.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1069_10218.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1069_10218.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1069_10218.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1069_10218.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1069_10218.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1069_10218.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1069_10218.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1069_10218.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1069_10218.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1069_10218.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1069_10218.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1069_10218.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1069_10218.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1069_10218.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1069_10218.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1069_10218.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1069_10218.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____10251 =
                                 let uu____10256 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____10256 with
                                 | (usubst, uvs1) ->
                                     let uu____10279 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____10280 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____10279, uu____10280) in
                               (match uu____10251 with
                                | (env2, lift2) ->
                                    let uu____10285 =
                                      let uu____10292 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____10292 in
                                    (match uu____10285 with
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
                                             let uu____10318 =
                                               let uu____10319 =
                                                 let uu____10336 =
                                                   let uu____10347 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____10356 =
                                                     let uu____10367 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____10367] in
                                                   uu____10347 :: uu____10356 in
                                                 (lift_wp1, uu____10336) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____10319 in
                                             let uu____10412 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____10318 uu____10412 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____10416 =
                                             let uu____10425 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____10432 =
                                               let uu____10441 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____10448 =
                                                 let uu____10457 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____10457] in
                                               uu____10441 :: uu____10448 in
                                             uu____10425 :: uu____10432 in
                                           let uu____10488 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____10416 uu____10488 in
                                         let uu____10491 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____10491 with
                                          | (expected_k2, uu____10501,
                                             uu____10502) ->
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
                                                   let uu____10510 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____10510)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____10518 =
                             let uu____10520 =
                               let uu____10522 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____10522
                                 FStar_List.length in
                             uu____10520 <> Prims.int_one in
                           if uu____10518
                           then
                             let uu____10545 =
                               let uu____10551 =
                                 let uu____10553 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____10555 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____10557 =
                                   let uu____10559 =
                                     let uu____10561 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____10561
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____10559
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10553 uu____10555 uu____10557 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10551) in
                             FStar_Errors.raise_error uu____10545 r
                           else ());
                          (let uu____10588 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10591 =
                                  let uu____10593 =
                                    let uu____10596 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____10596
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____10593
                                    FStar_List.length in
                                uu____10591 <> Prims.int_one) in
                           if uu____10588
                           then
                             let uu____10635 =
                               let uu____10641 =
                                 let uu____10643 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____10645 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____10647 =
                                   let uu____10649 =
                                     let uu____10651 =
                                       let uu____10654 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____10654
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____10651
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____10649
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10643 uu____10645 uu____10647 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10641) in
                             FStar_Errors.raise_error uu____10635 r
                           else ());
                          (let uu___1106_10696 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1106_10696.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1106_10696.FStar_Syntax_Syntax.target);
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
    fun uu____10727 ->
      fun r ->
        match uu____10727 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____10750 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10778 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____10778 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____10809 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____10809 c in
                     let uu____10818 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____10818, uvs1, tps1, c1)) in
            (match uu____10750 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____10838 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____10838 with
                  | (tps2, c2) ->
                      let uu____10853 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____10853 with
                       | (tps3, env3, us) ->
                           let uu____10871 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____10871 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____10897)::uu____10898 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10917 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____10925 =
                                    let uu____10927 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____10927 in
                                  if uu____10925
                                  then
                                    let uu____10930 =
                                      let uu____10936 =
                                        let uu____10938 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____10940 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10938 uu____10940 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10936) in
                                    FStar_Errors.raise_error uu____10930 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____10948 =
                                    let uu____10949 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10949 in
                                  match uu____10948 with
                                  | (uvs2, t) ->
                                      let uu____10978 =
                                        let uu____10983 =
                                          let uu____10996 =
                                            let uu____10997 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____10997.FStar_Syntax_Syntax.n in
                                          (tps4, uu____10996) in
                                        match uu____10983 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11012, c5)) -> ([], c5)
                                        | (uu____11054,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____11093 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____10978 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11125 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____11125 with
                                               | (uu____11130, t1) ->
                                                   let uu____11132 =
                                                     let uu____11138 =
                                                       let uu____11140 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____11142 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____11146 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11140
                                                         uu____11142
                                                         uu____11146 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11138) in
                                                   FStar_Errors.raise_error
                                                     uu____11132 r)
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
              let uu____11188 = FStar_Ident.string_of_lid m in
              let uu____11190 = FStar_Ident.string_of_lid n in
              let uu____11192 = FStar_Ident.string_of_lid p in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11188 uu____11190
                uu____11192 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____11200 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____11200 with
            | (us, t, ty) ->
                let uu____11216 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____11216 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____11229 =
                         let uu____11234 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____11234
                           (fun uu____11251 ->
                              match uu____11251 with
                              | (t1, u) ->
                                  let uu____11262 =
                                    let uu____11263 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____11263
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____11262, u)) in
                       match uu____11229 with
                       | (a, u_a) ->
                           let uu____11271 =
                             let uu____11276 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____11276
                               (fun uu____11293 ->
                                  match uu____11293 with
                                  | (t1, u) ->
                                      let uu____11304 =
                                        let uu____11305 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____11305
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____11304, u)) in
                           (match uu____11271 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____11322 =
                                    let uu____11323 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____11323.FStar_Syntax_Syntax.n in
                                  match uu____11322 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____11335) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11363 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____11363 with
                                       | (a', uu____11373)::(b', uu____11375)::bs1
                                           ->
                                           let uu____11405 =
                                             let uu____11406 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____11406
                                               FStar_Pervasives_Native.fst in
                                           let uu____11472 =
                                             let uu____11485 =
                                               let uu____11488 =
                                                 let uu____11489 =
                                                   let uu____11496 =
                                                     let uu____11499 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____11499
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____11496) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11489 in
                                               let uu____11512 =
                                                 let uu____11515 =
                                                   let uu____11516 =
                                                     let uu____11523 =
                                                       let uu____11526 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____11526
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____11523) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11516 in
                                                 [uu____11515] in
                                               uu____11488 :: uu____11512 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11485 in
                                           FStar_All.pipe_right uu____11405
                                             uu____11472)
                                  | uu____11547 ->
                                      let uu____11548 =
                                        let uu____11554 =
                                          let uu____11556 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____11558 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11556 uu____11558 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11554) in
                                      FStar_Errors.raise_error uu____11548 r in
                                let bs = a :: b :: rest_bs in
                                let uu____11591 =
                                  let uu____11602 =
                                    let uu____11607 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____11608 =
                                      let uu____11609 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____11609
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11607 r m u_a uu____11608 in
                                  match uu____11602 with
                                  | (repr, g) ->
                                      let uu____11630 =
                                        let uu____11637 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____11637
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____11630, g) in
                                (match uu____11591 with
                                 | (f, guard_f) ->
                                     let uu____11669 =
                                       let x_a =
                                         let uu____11687 =
                                           let uu____11688 =
                                             let uu____11689 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____11689
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11688 in
                                         FStar_All.pipe_right uu____11687
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____11705 =
                                         let uu____11710 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____11729 =
                                           let uu____11730 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____11730
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11710 r n u_b uu____11729 in
                                       match uu____11705 with
                                       | (repr, g) ->
                                           let uu____11751 =
                                             let uu____11758 =
                                               let uu____11759 =
                                                 let uu____11760 =
                                                   let uu____11763 =
                                                     let uu____11766 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11766 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11763 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11760 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11759 in
                                             FStar_All.pipe_right uu____11758
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____11751, g) in
                                     (match uu____11669 with
                                      | (g, guard_g) ->
                                          let uu____11810 =
                                            let uu____11815 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____11816 =
                                              let uu____11817 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____11817
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11815 r p u_b uu____11816 in
                                          (match uu____11810 with
                                           | (repr, guard_repr) ->
                                               let uu____11832 =
                                                 let uu____11837 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____11838 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____11837
                                                   repr uu____11838 r in
                                               (match uu____11832 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____11850 =
                                                        let uu____11853 =
                                                          let uu____11854 =
                                                            let uu____11855 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____11855] in
                                                          let uu____11856 =
                                                            let uu____11867 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____11867] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____11854;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____11856;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____11853 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____11850 in
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
                                                     (let uu____11927 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____11927
                                                      then
                                                        let uu____11931 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____11937 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____11931
                                                          uu____11937
                                                      else ());
                                                     (let uu____11947 =
                                                        let uu____11953 =
                                                          FStar_Util.format1
                                                            "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                            eff_name in
                                                        (FStar_Errors.Warning_BleedingEdge_Feature,
                                                          uu____11953) in
                                                      FStar_Errors.log_issue
                                                        r uu____11947);
                                                     (let uu____11957 =
                                                        let uu____11958 =
                                                          let uu____11961 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env1) in
                                                          FStar_All.pipe_right
                                                            uu____11961
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               us1) in
                                                        (us1, uu____11958) in
                                                      ((us1, t), uu____11957)))))))))))