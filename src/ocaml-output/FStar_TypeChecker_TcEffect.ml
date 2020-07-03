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
let (validate_layered_effect_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.term Prims.list ->
        Prims.bool -> FStar_Range.range -> unit)
  =
  fun env ->
    fun bs ->
      fun repr_terms ->
        fun check_non_informatve_binders ->
          fun r ->
            let repr_args repr =
              let uu____401 =
                let uu____402 = FStar_Syntax_Subst.compress repr in
                uu____402.FStar_Syntax_Syntax.n in
              match uu____401 with
              | FStar_Syntax_Syntax.Tm_app (uu____415, args) -> args
              | FStar_Syntax_Syntax.Tm_arrow (uu____441::[], c) ->
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_args
              | uu____483 ->
                  let uu____484 =
                    let uu____490 =
                      let uu____492 = FStar_Syntax_Print.term_to_string repr in
                      FStar_Util.format1
                        "Unexpected repr term %s when validating layered effect combinator binders"
                        uu____492 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____490) in
                  FStar_Errors.raise_error uu____484 r in
            let rec head_names_in_term arg =
              let uu____516 =
                let uu____517 = FStar_Syntax_Subst.compress arg in
                uu____517.FStar_Syntax_Syntax.n in
              match uu____516 with
              | FStar_Syntax_Syntax.Tm_name uu____524 -> [arg]
              | FStar_Syntax_Syntax.Tm_app (head, uu____530) ->
                  let uu____555 =
                    let uu____556 = FStar_Syntax_Subst.compress head in
                    uu____556.FStar_Syntax_Syntax.n in
                  (match uu____555 with
                   | FStar_Syntax_Syntax.Tm_name uu____563 -> [head]
                   | uu____568 -> [])
              | FStar_Syntax_Syntax.Tm_abs (uu____571, body, uu____573) ->
                  head_names_in_term body
              | uu____598 -> [] in
            let head_names_in_args args =
              let uu____627 =
                FStar_All.pipe_right args
                  (FStar_List.map FStar_Pervasives_Native.fst) in
              FStar_All.pipe_right uu____627
                (FStar_List.collect head_names_in_term) in
            let repr_names_args =
              FStar_List.collect
                (fun repr ->
                   let uu____666 = FStar_All.pipe_right repr repr_args in
                   FStar_All.pipe_right uu____666 head_names_in_args)
                repr_terms in
            (let uu____696 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____696
             then
               let uu____701 =
                 FStar_List.fold_left
                   (fun s ->
                      fun t ->
                        let uu____710 =
                          let uu____712 = FStar_Syntax_Print.term_to_string t in
                          Prims.op_Hat "; " uu____712 in
                        Prims.op_Hat s uu____710) "" repr_names_args in
               let uu____716 = FStar_Syntax_Print.binders_to_string "; " bs in
               FStar_Util.print2
                 "Checking layered effect combinator binders validity, names: %s, binders: %s\n\n"
                 uu____701 uu____716
             else ());
            (let valid_binder b =
               (FStar_List.existsb
                  (fun t ->
                     let uu____744 =
                       let uu____745 =
                         let uu____746 =
                           FStar_All.pipe_right b FStar_Pervasives_Native.fst in
                         FStar_All.pipe_right uu____746
                           FStar_Syntax_Syntax.bv_to_name in
                       FStar_Syntax_Util.eq_tm uu____745 t in
                     uu____744 = FStar_Syntax_Util.Equal) repr_names_args)
                 ||
                 (match FStar_Pervasives_Native.snd b with
                  | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                      (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                      uu____759)) -> true
                  | uu____763 -> false) in
             let invalid_binders =
               FStar_List.filter
                 (fun b -> Prims.op_Negation (valid_binder b)) bs in
             if (FStar_List.length invalid_binders) <> Prims.int_zero
             then
               (let uu____800 =
                  let uu____806 =
                    let uu____808 =
                      FStar_Syntax_Print.binders_to_string "; "
                        invalid_binders in
                    FStar_Util.format1
                      "Binders %s neither appear as repr indices nor have an associated tactic"
                      uu____808 in
                  (FStar_Errors.Fatal_UnexpectedEffect, uu____806) in
                FStar_Errors.raise_error uu____800 r)
             else ();
             if check_non_informatve_binders
             then
               (let uu____816 =
                  FStar_List.fold_left
                    (fun uu____853 ->
                       fun b ->
                         match uu____853 with
                         | (env1, bs1) ->
                             let env2 =
                               FStar_TypeChecker_Env.push_binders env1 [b] in
                             let uu____916 =
                               FStar_TypeChecker_Normalize.non_info_norm env2
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             if uu____916
                             then (env2, bs1)
                             else (env2, (b :: bs1))) (env, []) bs in
                match uu____816 with
                | (uu____971, informative_binders) ->
                    if
                      (FStar_List.length informative_binders) <>
                        Prims.int_zero
                    then
                      let uu____998 =
                        let uu____1004 =
                          let uu____1006 =
                            FStar_Syntax_Print.binders_to_string "; "
                              informative_binders in
                          FStar_Util.format1
                            "Binders %s are informative while the effect is reifiable"
                            uu____1006 in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____1004) in
                      FStar_Errors.raise_error uu____998 r
                    else ())
             else ())
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun quals ->
        fun attrs ->
          (let uu____1045 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
               (FStar_Options.Other "LayeredEffectsTc") in
           if uu____1045
           then
             let uu____1050 = FStar_Syntax_Print.eff_decl_to_string false ed in
             FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
               uu____1050
           else ());
          if
            ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <>
               Prims.int_zero)
              ||
              ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
                 Prims.int_zero)
          then
            (let uu____1068 =
               let uu____1074 =
                 let uu____1076 =
                   let uu____1078 =
                     FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                   Prims.op_Hat uu____1078 ")" in
                 Prims.op_Hat
                   "Binders are not supported for layered effects ("
                   uu____1076 in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____1074) in
             let uu____1083 =
               FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
             FStar_Errors.raise_error uu____1068 uu____1083)
          else ();
          (let log_combinator s uu____1109 =
             match uu____1109 with
             | (us, t, ty) ->
                 let uu____1138 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                     (FStar_Options.Other "LayeredEffectsTc") in
                 if uu____1138
                 then
                   let uu____1143 =
                     FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                   let uu____1145 =
                     FStar_Syntax_Print.tscheme_to_string (us, t) in
                   let uu____1151 =
                     FStar_Syntax_Print.tscheme_to_string (us, ty) in
                   FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____1143
                     s uu____1145 uu____1151
                 else () in
           let fresh_a_and_u_a a =
             let uu____1176 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____1176
               (fun uu____1193 ->
                  match uu____1193 with
                  | (t, u) ->
                      let uu____1204 =
                        let uu____1205 =
                          FStar_Syntax_Syntax.gen_bv a
                            FStar_Pervasives_Native.None t in
                        FStar_All.pipe_right uu____1205
                          FStar_Syntax_Syntax.mk_binder in
                      (uu____1204, u)) in
           let fresh_x_a x a =
             let uu____1219 =
               let uu____1220 =
                 let uu____1221 =
                   FStar_All.pipe_right a FStar_Pervasives_Native.fst in
                 FStar_All.pipe_right uu____1221
                   FStar_Syntax_Syntax.bv_to_name in
               FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
                 uu____1220 in
             FStar_All.pipe_right uu____1219 FStar_Syntax_Syntax.mk_binder in
           let check_and_gen1 =
             let uu____1255 =
               FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
             check_and_gen env0 uu____1255 in
           let signature =
             let r =
               (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
             let uu____1275 =
               check_and_gen1 "signature" Prims.int_one
                 ed.FStar_Syntax_Syntax.signature in
             match uu____1275 with
             | (sig_us, sig_t, sig_ty) ->
                 let uu____1299 =
                   FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
                 (match uu____1299 with
                  | (us, t) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                      let uu____1319 = fresh_a_and_u_a "a" in
                      (match uu____1319 with
                       | (a, u) ->
                           let rest_bs =
                             let uu____1340 =
                               let uu____1341 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____1341
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               (sig_us, sig_t) u uu____1340 in
                           let bs = a :: rest_bs in
                           let k =
                             let uu____1372 =
                               FStar_Syntax_Syntax.mk_Total
                                 FStar_Syntax_Syntax.teff in
                             FStar_Syntax_Util.arrow bs uu____1372 in
                           let g_eq = FStar_TypeChecker_Rel.teq env t k in
                           (FStar_TypeChecker_Rel.force_trivial_guard env
                              g_eq;
                            (let uu____1377 =
                               let uu____1380 =
                                 FStar_All.pipe_right k
                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                      env) in
                               FStar_Syntax_Subst.close_univ_vars us
                                 uu____1380 in
                             (sig_us, uu____1377, sig_ty))))) in
           log_combinator "signature" signature;
           (let repr =
              let repr_ts =
                let uu____1407 =
                  FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                FStar_All.pipe_right uu____1407 FStar_Util.must in
              let r =
                (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
              let uu____1435 = check_and_gen1 "repr" Prims.int_one repr_ts in
              match uu____1435 with
              | (repr_us, repr_t, repr_ty) ->
                  let uu____1459 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                  (match uu____1459 with
                   | (us, ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                       let uu____1479 = fresh_a_and_u_a "a" in
                       (match uu____1479 with
                        | (a, u) ->
                            let rest_bs =
                              let signature_ts =
                                let uu____1501 = signature in
                                match uu____1501 with
                                | (us1, t, uu____1516) -> (us1, t) in
                              let uu____1533 =
                                let uu____1534 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst in
                                FStar_All.pipe_right uu____1534
                                  FStar_Syntax_Syntax.bv_to_name in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                env r ed.FStar_Syntax_Syntax.mname
                                signature_ts u uu____1533 in
                            let bs = a :: rest_bs in
                            let k =
                              let uu____1561 =
                                let uu____1564 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____1564
                                  (fun uu____1577 ->
                                     match uu____1577 with
                                     | (t, u1) ->
                                         let uu____1584 =
                                           let uu____1587 =
                                             FStar_TypeChecker_Env.new_u_univ
                                               () in
                                           FStar_Pervasives_Native.Some
                                             uu____1587 in
                                         FStar_Syntax_Syntax.mk_Total' t
                                           uu____1584) in
                              FStar_Syntax_Util.arrow bs uu____1561 in
                            let g = FStar_TypeChecker_Rel.teq env ty k in
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             (let uu____1590 =
                                let uu____1593 =
                                  FStar_All.pipe_right k
                                    (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       env) in
                                FStar_Syntax_Subst.close_univ_vars us
                                  uu____1593 in
                              (repr_us, repr_t, uu____1590))))) in
            log_combinator "repr" repr;
            (let fresh_repr r env u a_tm =
               let signature_ts =
                 let uu____1628 = signature in
                 match uu____1628 with | (us, t, uu____1643) -> (us, t) in
               let repr_ts =
                 let uu____1661 = repr in
                 match uu____1661 with | (us, t, uu____1676) -> (us, t) in
               FStar_TypeChecker_Util.fresh_effect_repr env r
                 ed.FStar_Syntax_Syntax.mname signature_ts
                 (FStar_Pervasives_Native.Some repr_ts) u a_tm in
             let not_an_arrow_error comb n t r =
               let uu____1726 =
                 let uu____1732 =
                   let uu____1734 =
                     FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                   let uu____1736 = FStar_Util.string_of_int n in
                   let uu____1738 = FStar_Syntax_Print.tag_of_term t in
                   let uu____1740 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.format5
                     "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                     uu____1734 comb uu____1736 uu____1738 uu____1740 in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____1732) in
               FStar_Errors.raise_error uu____1726 r in
             let check_non_informative_binders =
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals) &&
                 (let uu____1755 =
                    FStar_Syntax_Util.has_attribute attrs
                      FStar_Parser_Const.allow_informative_binders_attr in
                  Prims.op_Negation uu____1755) in
             let return_repr =
               let return_repr_ts =
                 let uu____1775 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
                 FStar_All.pipe_right uu____1775 FStar_Util.must in
               let r =
                 (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
               let uu____1787 =
                 check_and_gen1 "return_repr" Prims.int_one return_repr_ts in
               match uu____1787 with
               | (ret_us, ret_t, ret_ty) ->
                   let uu____1811 =
                     FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                   (match uu____1811 with
                    | (us, ty) ->
                        let env =
                          FStar_TypeChecker_Env.push_univ_vars env0 us in
                        (check_no_subtyping_for_layered_combinator env ty
                           FStar_Pervasives_Native.None;
                         (let uu____1832 = fresh_a_and_u_a "a" in
                          match uu____1832 with
                          | (a, u_a) ->
                              let x_a = fresh_x_a "x" a in
                              let rest_bs =
                                let uu____1863 =
                                  let uu____1864 =
                                    FStar_Syntax_Subst.compress ty in
                                  uu____1864.FStar_Syntax_Syntax.n in
                                match uu____1863 with
                                | FStar_Syntax_Syntax.Tm_arrow
                                    (bs, uu____1876) when
                                    (FStar_List.length bs) >=
                                      (Prims.of_int (2))
                                    ->
                                    let uu____1904 =
                                      FStar_Syntax_Subst.open_binders bs in
                                    (match uu____1904 with
                                     | (a', uu____1914)::(x', uu____1916)::bs1
                                         ->
                                         let uu____1946 =
                                           let uu____1947 =
                                             let uu____1952 =
                                               let uu____1955 =
                                                 let uu____1956 =
                                                   let uu____1963 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          a) in
                                                   (a', uu____1963) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1956 in
                                               [uu____1955] in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1952 in
                                           FStar_All.pipe_right bs1
                                             uu____1947 in
                                         let uu____1970 =
                                           let uu____1983 =
                                             let uu____1986 =
                                               let uu____1987 =
                                                 let uu____1994 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        x_a) in
                                                 (x', uu____1994) in
                                               FStar_Syntax_Syntax.NT
                                                 uu____1987 in
                                             [uu____1986] in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____1983 in
                                         FStar_All.pipe_right uu____1946
                                           uu____1970)
                                | uu____2009 ->
                                    not_an_arrow_error "return"
                                      (Prims.of_int (2)) ty r in
                              let bs = a :: x_a :: rest_bs in
                              let uu____2033 =
                                let uu____2038 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____2039 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name in
                                fresh_repr r uu____2038 u_a uu____2039 in
                              (match uu____2033 with
                               | (repr1, g) ->
                                   let k =
                                     let uu____2059 =
                                       FStar_Syntax_Syntax.mk_Total' repr1
                                         (FStar_Pervasives_Native.Some u_a) in
                                     FStar_Syntax_Util.arrow bs uu____2059 in
                                   let g_eq =
                                     FStar_TypeChecker_Rel.teq env ty k in
                                   ((let uu____2064 =
                                       FStar_TypeChecker_Env.conj_guard g
                                         g_eq in
                                     FStar_TypeChecker_Rel.force_trivial_guard
                                       env uu____2064);
                                    (let k1 =
                                       FStar_All.pipe_right k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env) in
                                     (let uu____2067 =
                                        let uu____2068 =
                                          FStar_Syntax_Subst.compress k1 in
                                        uu____2068.FStar_Syntax_Syntax.n in
                                      match uu____2067 with
                                      | FStar_Syntax_Syntax.Tm_arrow 
                                          (bs1, c) ->
                                          let uu____2093 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              c in
                                          (match uu____2093 with
                                           | (a1::x::bs2, c1) ->
                                               let res_t =
                                                 FStar_Syntax_Util.comp_result
                                                   c1 in
                                               let env1 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env [a1; x] in
                                               validate_layered_effect_binders
                                                 env1 bs2 [res_t]
                                                 check_non_informative_binders
                                                 r));
                                     (let uu____2156 =
                                        FStar_All.pipe_right k1
                                          (FStar_Syntax_Subst.close_univ_vars
                                             us) in
                                      (ret_us, ret_t, uu____2156)))))))) in
             log_combinator "return_repr" return_repr;
             (let bind_repr =
                let bind_repr_ts =
                  let uu____2187 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                  FStar_All.pipe_right uu____2187 FStar_Util.must in
                let r =
                  (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
                let uu____2215 =
                  check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
                match uu____2215 with
                | (bind_us, bind_t, bind_ty) ->
                    let uu____2239 =
                      FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                    (match uu____2239 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2260 = fresh_a_and_u_a "a" in
                           match uu____2260 with
                           | (a, u_a) ->
                               let uu____2280 = fresh_a_and_u_a "b" in
                               (match uu____2280 with
                                | (b, u_b) ->
                                    let rest_bs =
                                      let uu____2309 =
                                        let uu____2310 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____2310.FStar_Syntax_Syntax.n in
                                      match uu____2309 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____2322) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____2350 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____2350 with
                                           | (a', uu____2360)::(b',
                                                                uu____2362)::bs1
                                               ->
                                               let uu____2392 =
                                                 let uu____2393 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (2)))) in
                                                 FStar_All.pipe_right
                                                   uu____2393
                                                   FStar_Pervasives_Native.fst in
                                               let uu____2459 =
                                                 let uu____2472 =
                                                   let uu____2475 =
                                                     let uu____2476 =
                                                       let uu____2483 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a) in
                                                       (a', uu____2483) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2476 in
                                                   let uu____2490 =
                                                     let uu____2493 =
                                                       let uu____2494 =
                                                         let uu____2501 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                b) in
                                                         (b', uu____2501) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____2494 in
                                                     [uu____2493] in
                                                   uu____2475 :: uu____2490 in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2472 in
                                               FStar_All.pipe_right
                                                 uu____2392 uu____2459)
                                      | uu____2516 ->
                                          not_an_arrow_error "bind"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: b :: rest_bs in
                                    let uu____2540 =
                                      let uu____2551 =
                                        let uu____2556 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____2557 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____2556 u_a
                                          uu____2557 in
                                      match uu____2551 with
                                      | (repr1, g) ->
                                          let uu____2572 =
                                            let uu____2579 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____2579
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____2572, g) in
                                    (match uu____2540 with
                                     | (f, guard_f) ->
                                         let uu____2619 =
                                           let x_a = fresh_x_a "x" a in
                                           let uu____2632 =
                                             let uu____2637 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env
                                                 (FStar_List.append bs [x_a]) in
                                             let uu____2656 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    b)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____2637 u_b
                                               uu____2656 in
                                           match uu____2632 with
                                           | (repr1, g) ->
                                               let uu____2671 =
                                                 let uu____2678 =
                                                   let uu____2679 =
                                                     let uu____2680 =
                                                       let uu____2683 =
                                                         let uu____2686 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             () in
                                                         FStar_Pervasives_Native.Some
                                                           uu____2686 in
                                                       FStar_Syntax_Syntax.mk_Total'
                                                         repr1 uu____2683 in
                                                     FStar_Syntax_Util.arrow
                                                       [x_a] uu____2680 in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     uu____2679 in
                                                 FStar_All.pipe_right
                                                   uu____2678
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____2671, g) in
                                         (match uu____2619 with
                                          | (g, guard_g) ->
                                              let uu____2738 =
                                                let uu____2743 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs in
                                                let uu____2744 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____2743 u_b
                                                  uu____2744 in
                                              (match uu____2738 with
                                               | (repr1, guard_repr) ->
                                                   let uu____2761 =
                                                     let uu____2766 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env bs in
                                                     let uu____2767 =
                                                       let uu____2769 =
                                                         FStar_Ident.string_of_lid
                                                           ed.FStar_Syntax_Syntax.mname in
                                                       FStar_Util.format1
                                                         "implicit for pure_wp in checking bind for %s"
                                                         uu____2769 in
                                                     pure_wp_uvar uu____2766
                                                       repr1 uu____2767 r in
                                                   (match uu____2761 with
                                                    | (pure_wp_uvar1,
                                                       g_pure_wp_uvar) ->
                                                        let k =
                                                          let uu____2789 =
                                                            let uu____2792 =
                                                              let uu____2793
                                                                =
                                                                let uu____2794
                                                                  =
                                                                  FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                [uu____2794] in
                                                              let uu____2795
                                                                =
                                                                let uu____2806
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____2806] in
                                                              {
                                                                FStar_Syntax_Syntax.comp_univs
                                                                  =
                                                                  uu____2793;
                                                                FStar_Syntax_Syntax.effect_name
                                                                  =
                                                                  FStar_Parser_Const.effect_PURE_lid;
                                                                FStar_Syntax_Syntax.result_typ
                                                                  = repr1;
                                                                FStar_Syntax_Syntax.effect_args
                                                                  =
                                                                  uu____2795;
                                                                FStar_Syntax_Syntax.flags
                                                                  = []
                                                              } in
                                                            FStar_Syntax_Syntax.mk_Comp
                                                              uu____2792 in
                                                          FStar_Syntax_Util.arrow
                                                            (FStar_List.append
                                                               bs [f; g])
                                                            uu____2789 in
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
                                                         (let k1 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env) in
                                                          (let uu____2867 =
                                                             let uu____2868 =
                                                               FStar_Syntax_Subst.compress
                                                                 k1 in
                                                             uu____2868.FStar_Syntax_Syntax.n in
                                                           match uu____2867
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1, c) ->
                                                               let uu____2893
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c in
                                                               (match uu____2893
                                                                with
                                                                | (a1::b1::bs2,
                                                                   c1) ->
                                                                    let res_t
                                                                    =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                    let uu____2937
                                                                    =
                                                                    let uu____2964
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____2964
                                                                    (fun
                                                                    uu____3049
                                                                    ->
                                                                    match uu____3049
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____3130
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____3157
                                                                    =
                                                                    let uu____3164
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____3164
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____3130,
                                                                    uu____3157)) in
                                                                    (match uu____2937
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____3279
                                                                    =
                                                                    let uu____3280
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____3280.FStar_Syntax_Syntax.n in
                                                                    match uu____3279
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____3285,
                                                                    c2) ->
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env
                                                                    [a1; b1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    g_sort;
                                                                    res_t]
                                                                    check_non_informative_binders
                                                                    r)));
                                                          (let uu____3328 =
                                                             FStar_All.pipe_right
                                                               k1
                                                               (FStar_Syntax_Subst.close_univ_vars
                                                                  bind_us) in
                                                           (bind_us, bind_t,
                                                             uu____3328)))))))))))) in
              log_combinator "bind_repr" bind_repr;
              (let stronger_repr =
                 let stronger_repr =
                   let ts =
                     let uu____3364 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_stronger_repr in
                     FStar_All.pipe_right uu____3364 FStar_Util.must in
                   let uu____3391 =
                     let uu____3392 =
                       let uu____3395 =
                         FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____3395
                         FStar_Syntax_Subst.compress in
                     uu____3392.FStar_Syntax_Syntax.n in
                   match uu____3391 with
                   | FStar_Syntax_Syntax.Tm_unknown ->
                       let signature_ts =
                         let uu____3407 = signature in
                         match uu____3407 with
                         | (us, t, uu____3422) -> (us, t) in
                       let uu____3439 =
                         FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                           [FStar_Syntax_Syntax.U_unknown] in
                       (match uu____3439 with
                        | (uu____3448, signature_t) ->
                            let uu____3450 =
                              let uu____3451 =
                                FStar_Syntax_Subst.compress signature_t in
                              uu____3451.FStar_Syntax_Syntax.n in
                            (match uu____3450 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3459)
                                 ->
                                 let bs1 = FStar_Syntax_Subst.open_binders bs in
                                 let repr_t =
                                   let repr_ts =
                                     let uu____3485 = repr in
                                     match uu____3485 with
                                     | (us, t, uu____3500) -> (us, t) in
                                   let uu____3517 =
                                     FStar_TypeChecker_Env.inst_tscheme_with
                                       repr_ts
                                       [FStar_Syntax_Syntax.U_unknown] in
                                   FStar_All.pipe_right uu____3517
                                     FStar_Pervasives_Native.snd in
                                 let repr_t_applied =
                                   let uu____3531 =
                                     let uu____3532 =
                                       let uu____3549 =
                                         let uu____3560 =
                                           let uu____3563 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst) in
                                           FStar_All.pipe_right uu____3563
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name) in
                                         FStar_All.pipe_right uu____3560
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.as_arg) in
                                       (repr_t, uu____3549) in
                                     FStar_Syntax_Syntax.Tm_app uu____3532 in
                                   FStar_Syntax_Syntax.mk uu____3531
                                     FStar_Range.dummyRange in
                                 let f_b =
                                   FStar_Syntax_Syntax.null_binder
                                     repr_t_applied in
                                 let uu____3613 =
                                   let uu____3614 =
                                     let uu____3617 =
                                       FStar_All.pipe_right f_b
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____3617
                                       FStar_Syntax_Syntax.bv_to_name in
                                   FStar_Syntax_Util.abs
                                     (FStar_List.append bs1 [f_b]) uu____3614
                                     FStar_Pervasives_Native.None in
                                 ([], uu____3613)
                             | uu____3646 -> failwith "Impossible!"))
                   | uu____3652 -> ts in
                 let r =
                   (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
                 let uu____3654 =
                   check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
                 match uu____3654 with
                 | (stronger_us, stronger_t, stronger_ty) ->
                     ((let uu____3679 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "LayeredEffectsTc") in
                       if uu____3679
                       then
                         let uu____3684 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_t) in
                         let uu____3690 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_ty) in
                         FStar_Util.print2
                           "stronger combinator typechecked with term: %s and type: %s\n"
                           uu____3684 uu____3690
                       else ());
                      (let uu____3699 =
                         FStar_Syntax_Subst.open_univ_vars stronger_us
                           stronger_ty in
                       match uu____3699 with
                       | (us, ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____3720 = fresh_a_and_u_a "a" in
                             match uu____3720 with
                             | (a, u) ->
                                 let rest_bs =
                                   let uu____3749 =
                                     let uu____3750 =
                                       FStar_Syntax_Subst.compress ty in
                                     uu____3750.FStar_Syntax_Syntax.n in
                                   match uu____3749 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs, uu____3762) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____3790 =
                                         FStar_Syntax_Subst.open_binders bs in
                                       (match uu____3790 with
                                        | (a', uu____3800)::bs1 ->
                                            let uu____3820 =
                                              let uu____3821 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one)) in
                                              FStar_All.pipe_right uu____3821
                                                FStar_Pervasives_Native.fst in
                                            let uu____3919 =
                                              let uu____3932 =
                                                let uu____3935 =
                                                  let uu____3936 =
                                                    let uu____3943 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           a) in
                                                    (a', uu____3943) in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3936 in
                                                [uu____3935] in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____3932 in
                                            FStar_All.pipe_right uu____3820
                                              uu____3919)
                                   | uu____3958 ->
                                       not_an_arrow_error "stronger"
                                         (Prims.of_int (2)) ty r in
                                 let bs = a :: rest_bs in
                                 let uu____3976 =
                                   let uu____3987 =
                                     let uu____3992 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____3993 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name in
                                     fresh_repr r uu____3992 u uu____3993 in
                                   match uu____3987 with
                                   | (repr1, g) ->
                                       let uu____4008 =
                                         let uu____4015 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr1 in
                                         FStar_All.pipe_right uu____4015
                                           FStar_Syntax_Syntax.mk_binder in
                                       (uu____4008, g) in
                                 (match uu____3976 with
                                  | (f, guard_f) ->
                                      let uu____4055 =
                                        let uu____4060 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____4061 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____4060 u uu____4061 in
                                      (match uu____4055 with
                                       | (ret_t, guard_ret_t) ->
                                           let uu____4078 =
                                             let uu____4083 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____4084 =
                                               let uu____4086 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               FStar_Util.format1
                                                 "implicit for pure_wp in checking stronger for %s"
                                                 uu____4086 in
                                             pure_wp_uvar uu____4083 ret_t
                                               uu____4084 r in
                                           (match uu____4078 with
                                            | (pure_wp_uvar1, guard_wp) ->
                                                let c =
                                                  let uu____4104 =
                                                    let uu____4105 =
                                                      let uu____4106 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          () in
                                                      [uu____4106] in
                                                    let uu____4107 =
                                                      let uu____4118 =
                                                        FStar_All.pipe_right
                                                          pure_wp_uvar1
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____4118] in
                                                    {
                                                      FStar_Syntax_Syntax.comp_univs
                                                        = uu____4105;
                                                      FStar_Syntax_Syntax.effect_name
                                                        =
                                                        FStar_Parser_Const.effect_PURE_lid;
                                                      FStar_Syntax_Syntax.result_typ
                                                        = ret_t;
                                                      FStar_Syntax_Syntax.effect_args
                                                        = uu____4107;
                                                      FStar_Syntax_Syntax.flags
                                                        = []
                                                    } in
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    uu____4104 in
                                                let k =
                                                  FStar_Syntax_Util.arrow
                                                    (FStar_List.append bs [f])
                                                    c in
                                                ((let uu____4173 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env)
                                                      (FStar_Options.Other
                                                         "LayeredEffectsTc") in
                                                  if uu____4173
                                                  then
                                                    let uu____4178 =
                                                      FStar_Syntax_Print.term_to_string
                                                        k in
                                                    FStar_Util.print1
                                                      "Expected type of subcomp before unification: %s\n"
                                                      uu____4178
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
                                                  (let k1 =
                                                     let uu____4186 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____4186
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   (let uu____4188 =
                                                      let uu____4189 =
                                                        FStar_Syntax_Subst.compress
                                                          k1 in
                                                      uu____4189.FStar_Syntax_Syntax.n in
                                                    match uu____4188 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs1, c1) ->
                                                        let uu____4214 =
                                                          FStar_Syntax_Subst.open_comp
                                                            bs1 c1 in
                                                        (match uu____4214
                                                         with
                                                         | (a1::bs2, c2) ->
                                                             let res_t =
                                                               FStar_Syntax_Util.comp_result
                                                                 c2 in
                                                             let uu____4245 =
                                                               let uu____4264
                                                                 =
                                                                 FStar_List.splitAt
                                                                   ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                   bs2 in
                                                               FStar_All.pipe_right
                                                                 uu____4264
                                                                 (fun
                                                                    uu____4340
                                                                    ->
                                                                    match uu____4340
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____4413
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu____4413)) in
                                                             (match uu____4245
                                                              with
                                                              | (bs3, f_b) ->
                                                                  let env1 =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [a1] in
                                                                  validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    res_t]
                                                                    check_non_informative_binders
                                                                    r)));
                                                   (let uu____4485 =
                                                      FStar_All.pipe_right k1
                                                        (FStar_Syntax_Subst.close_univ_vars
                                                           stronger_us) in
                                                    (stronger_us, stronger_t,
                                                      uu____4485)))))))))))) in
               log_combinator "stronger_repr" stronger_repr;
               (let if_then_else =
                  let if_then_else_ts =
                    let ts =
                      let uu____4521 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____4521 FStar_Util.must in
                    let uu____4548 =
                      let uu____4549 =
                        let uu____4552 =
                          FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                        FStar_All.pipe_right uu____4552
                          FStar_Syntax_Subst.compress in
                      uu____4549.FStar_Syntax_Syntax.n in
                    match uu____4548 with
                    | FStar_Syntax_Syntax.Tm_unknown ->
                        let signature_ts =
                          let uu____4564 = signature in
                          match uu____4564 with
                          | (us, t, uu____4579) -> (us, t) in
                        let uu____4596 =
                          FStar_TypeChecker_Env.inst_tscheme_with
                            signature_ts [FStar_Syntax_Syntax.U_unknown] in
                        (match uu____4596 with
                         | (uu____4605, signature_t) ->
                             let uu____4607 =
                               let uu____4608 =
                                 FStar_Syntax_Subst.compress signature_t in
                               uu____4608.FStar_Syntax_Syntax.n in
                             (match uu____4607 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4616)
                                  ->
                                  let bs1 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  let repr_t =
                                    let repr_ts =
                                      let uu____4642 = repr in
                                      match uu____4642 with
                                      | (us, t, uu____4657) -> (us, t) in
                                    let uu____4674 =
                                      FStar_TypeChecker_Env.inst_tscheme_with
                                        repr_ts
                                        [FStar_Syntax_Syntax.U_unknown] in
                                    FStar_All.pipe_right uu____4674
                                      FStar_Pervasives_Native.snd in
                                  let repr_t_applied =
                                    let uu____4688 =
                                      let uu____4689 =
                                        let uu____4706 =
                                          let uu____4717 =
                                            let uu____4720 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.map
                                                   FStar_Pervasives_Native.fst) in
                                            FStar_All.pipe_right uu____4720
                                              (FStar_List.map
                                                 FStar_Syntax_Syntax.bv_to_name) in
                                          FStar_All.pipe_right uu____4717
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.as_arg) in
                                        (repr_t, uu____4706) in
                                      FStar_Syntax_Syntax.Tm_app uu____4689 in
                                    FStar_Syntax_Syntax.mk uu____4688
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
                                  let uu____4772 =
                                    FStar_Syntax_Util.abs
                                      (FStar_List.append bs1 [f_b; g_b; b_b])
                                      repr_t_applied
                                      FStar_Pervasives_Native.None in
                                  ([], uu____4772)
                              | uu____4803 -> failwith "Impossible!"))
                    | uu____4809 -> ts in
                  let r =
                    (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                  let uu____4811 =
                    check_and_gen1 "if_then_else" Prims.int_one
                      if_then_else_ts in
                  match uu____4811 with
                  | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                      let uu____4835 =
                        FStar_Syntax_Subst.open_univ_vars if_then_else_us
                          if_then_else_t in
                      (match uu____4835 with
                       | (us, t) ->
                           let uu____4854 =
                             FStar_Syntax_Subst.open_univ_vars
                               if_then_else_us if_then_else_ty in
                           (match uu____4854 with
                            | (uu____4871, ty) ->
                                let env =
                                  FStar_TypeChecker_Env.push_univ_vars env0
                                    us in
                                (check_no_subtyping_for_layered_combinator
                                   env t (FStar_Pervasives_Native.Some ty);
                                 (let uu____4875 = fresh_a_and_u_a "a" in
                                  match uu____4875 with
                                  | (a, u_a) ->
                                      let rest_bs =
                                        let uu____4904 =
                                          let uu____4905 =
                                            FStar_Syntax_Subst.compress ty in
                                          uu____4905.FStar_Syntax_Syntax.n in
                                        match uu____4904 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu____4917) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____4945 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            (match uu____4945 with
                                             | (a', uu____4955)::bs1 ->
                                                 let uu____4975 =
                                                   let uu____4976 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (3)))) in
                                                   FStar_All.pipe_right
                                                     uu____4976
                                                     FStar_Pervasives_Native.fst in
                                                 let uu____5042 =
                                                   let uu____5055 =
                                                     let uu____5058 =
                                                       let uu____5059 =
                                                         let uu____5066 =
                                                           let uu____5069 =
                                                             FStar_All.pipe_right
                                                               a
                                                               FStar_Pervasives_Native.fst in
                                                           FStar_All.pipe_right
                                                             uu____5069
                                                             FStar_Syntax_Syntax.bv_to_name in
                                                         (a', uu____5066) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____5059 in
                                                     [uu____5058] in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____5055 in
                                                 FStar_All.pipe_right
                                                   uu____4975 uu____5042)
                                        | uu____5090 ->
                                            not_an_arrow_error "if_then_else"
                                              (Prims.of_int (4)) ty r in
                                      let bs = a :: rest_bs in
                                      let uu____5108 =
                                        let uu____5119 =
                                          let uu____5124 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs in
                                          let uu____5125 =
                                            let uu____5126 =
                                              FStar_All.pipe_right a
                                                FStar_Pervasives_Native.fst in
                                            FStar_All.pipe_right uu____5126
                                              FStar_Syntax_Syntax.bv_to_name in
                                          fresh_repr r uu____5124 u_a
                                            uu____5125 in
                                        match uu____5119 with
                                        | (repr1, g) ->
                                            let uu____5147 =
                                              let uu____5154 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1 in
                                              FStar_All.pipe_right uu____5154
                                                FStar_Syntax_Syntax.mk_binder in
                                            (uu____5147, g) in
                                      (match uu____5108 with
                                       | (f_bs, guard_f) ->
                                           let uu____5194 =
                                             let uu____5205 =
                                               let uu____5210 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs in
                                               let uu____5211 =
                                                 let uu____5212 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst in
                                                 FStar_All.pipe_right
                                                   uu____5212
                                                   FStar_Syntax_Syntax.bv_to_name in
                                               fresh_repr r uu____5210 u_a
                                                 uu____5211 in
                                             match uu____5205 with
                                             | (repr1, g) ->
                                                 let uu____5233 =
                                                   let uu____5240 =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       repr1 in
                                                   FStar_All.pipe_right
                                                     uu____5240
                                                     FStar_Syntax_Syntax.mk_binder in
                                                 (uu____5233, g) in
                                           (match uu____5194 with
                                            | (g_bs, guard_g) ->
                                                let p_b =
                                                  let uu____5287 =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "p"
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.t_bool in
                                                  FStar_All.pipe_right
                                                    uu____5287
                                                    FStar_Syntax_Syntax.mk_binder in
                                                let uu____5295 =
                                                  let uu____5300 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env
                                                      (FStar_List.append bs
                                                         [p_b]) in
                                                  let uu____5319 =
                                                    let uu____5320 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst in
                                                    FStar_All.pipe_right
                                                      uu____5320
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  fresh_repr r uu____5300 u_a
                                                    uu____5319 in
                                                (match uu____5295 with
                                                 | (t_body, guard_body) ->
                                                     let k =
                                                       FStar_Syntax_Util.abs
                                                         (FStar_List.append
                                                            bs
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
                                                      (let k1 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env) in
                                                       (let uu____5382 =
                                                          let uu____5383 =
                                                            FStar_Syntax_Subst.compress
                                                              k1 in
                                                          uu____5383.FStar_Syntax_Syntax.n in
                                                        match uu____5382 with
                                                        | FStar_Syntax_Syntax.Tm_abs
                                                            (bs1, body,
                                                             uu____5388)
                                                            ->
                                                            let uu____5413 =
                                                              FStar_Syntax_Subst.open_term
                                                                bs1 body in
                                                            (match uu____5413
                                                             with
                                                             | (a1::bs2,
                                                                body1) ->
                                                                 let uu____5441
                                                                   =
                                                                   let uu____5468
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                   FStar_All.pipe_right
                                                                    uu____5468
                                                                    (fun
                                                                    uu____5553
                                                                    ->
                                                                    match uu____5553
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5634
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5661
                                                                    =
                                                                    let uu____5668
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5668
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____5634,
                                                                    uu____5661)) in
                                                                 (match uu____5441
                                                                  with
                                                                  | (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let env1
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env 
                                                                    [a1] in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort;
                                                                    body1]
                                                                    check_non_informative_binders
                                                                    r)));
                                                       (let uu____5799 =
                                                          FStar_All.pipe_right
                                                            k1
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               if_then_else_us) in
                                                        (if_then_else_us,
                                                          uu____5799,
                                                          if_then_else_ty))))))))))) in
                log_combinator "if_then_else" if_then_else;
                (let r =
                   let uu____5814 =
                     let uu____5817 =
                       let uu____5826 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator in
                       FStar_All.pipe_right uu____5826 FStar_Util.must in
                     FStar_All.pipe_right uu____5817
                       FStar_Pervasives_Native.snd in
                   uu____5814.FStar_Syntax_Syntax.pos in
                 let binder_aq_to_arg_aq aq =
                   match aq with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5901) -> aq
                   | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                       uu____5903) ->
                       FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit false)
                   | uu____5905 -> FStar_Pervasives_Native.None in
                 let uu____5908 = if_then_else in
                 match uu____5908 with
                 | (ite_us, ite_t, uu____5923) ->
                     let uu____5936 =
                       FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                     (match uu____5936 with
                      | (us, ite_t1) ->
                          let uu____5943 =
                            let uu____5960 =
                              let uu____5961 =
                                FStar_Syntax_Subst.compress ite_t1 in
                              uu____5961.FStar_Syntax_Syntax.n in
                            match uu____5960 with
                            | FStar_Syntax_Syntax.Tm_abs
                                (bs, uu____5981, uu____5982) ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs in
                                let uu____6008 =
                                  let uu____6021 =
                                    let uu____6026 =
                                      let uu____6029 =
                                        let uu____6038 =
                                          FStar_All.pipe_right bs1
                                            (FStar_List.splitAt
                                               ((FStar_List.length bs1) -
                                                  (Prims.of_int (3)))) in
                                        FStar_All.pipe_right uu____6038
                                          FStar_Pervasives_Native.snd in
                                      FStar_All.pipe_right uu____6029
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    FStar_All.pipe_right uu____6026
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.bv_to_name) in
                                  FStar_All.pipe_right uu____6021
                                    (fun l ->
                                       let uu____6194 = l in
                                       match uu____6194 with
                                       | f::g::p::[] -> (f, g, p)) in
                                (match uu____6008 with
                                 | (f, g, p) ->
                                     let uu____6265 =
                                       let uu____6266 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env0 us in
                                       FStar_TypeChecker_Env.push_binders
                                         uu____6266 bs1 in
                                     let uu____6267 =
                                       let uu____6268 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.map
                                              (fun uu____6293 ->
                                                 match uu____6293 with
                                                 | (b, qual) ->
                                                     let uu____6312 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     (uu____6312,
                                                       (binder_aq_to_arg_aq
                                                          qual)))) in
                                       FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                         uu____6268 r in
                                     (uu____6265, uu____6267, f, g, p))
                            | uu____6321 ->
                                failwith
                                  "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                          (match uu____5943 with
                           | (env, ite_t_applied, f_t, g_t, p_t) ->
                               let uu____6356 =
                                 let uu____6365 = stronger_repr in
                                 match uu____6365 with
                                 | (uu____6386, subcomp_t, subcomp_ty) ->
                                     let uu____6401 =
                                       FStar_Syntax_Subst.open_univ_vars us
                                         subcomp_t in
                                     (match uu____6401 with
                                      | (uu____6414, subcomp_t1) ->
                                          let uu____6416 =
                                            let uu____6427 =
                                              FStar_Syntax_Subst.open_univ_vars
                                                us subcomp_ty in
                                            match uu____6427 with
                                            | (uu____6442, subcomp_ty1) ->
                                                let uu____6444 =
                                                  let uu____6445 =
                                                    FStar_Syntax_Subst.compress
                                                      subcomp_ty1 in
                                                  uu____6445.FStar_Syntax_Syntax.n in
                                                (match uu____6444 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs, uu____6459) ->
                                                     let uu____6480 =
                                                       FStar_All.pipe_right
                                                         bs
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs)
                                                               -
                                                               Prims.int_one)) in
                                                     (match uu____6480 with
                                                      | (bs_except_last,
                                                         last_b) ->
                                                          let uu____6586 =
                                                            FStar_All.pipe_right
                                                              bs_except_last
                                                              (FStar_List.map
                                                                 FStar_Pervasives_Native.snd) in
                                                          let uu____6613 =
                                                            let uu____6616 =
                                                              FStar_All.pipe_right
                                                                last_b
                                                                FStar_List.hd in
                                                            FStar_All.pipe_right
                                                              uu____6616
                                                              FStar_Pervasives_Native.snd in
                                                          (uu____6586,
                                                            uu____6613))
                                                 | uu____6659 ->
                                                     failwith
                                                       "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                          (match uu____6416 with
                                           | (aqs_except_last, last_aq) ->
                                               let uu____6693 =
                                                 let uu____6704 =
                                                   FStar_All.pipe_right
                                                     aqs_except_last
                                                     (FStar_List.map
                                                        binder_aq_to_arg_aq) in
                                                 let uu____6721 =
                                                   FStar_All.pipe_right
                                                     last_aq
                                                     binder_aq_to_arg_aq in
                                                 (uu____6704, uu____6721) in
                                               (match uu____6693 with
                                                | (aqs_except_last1,
                                                   last_aq1) ->
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
                                                    let uu____6833 = aux f_t in
                                                    let uu____6836 = aux g_t in
                                                    (uu____6833, uu____6836)))) in
                               (match uu____6356 with
                                | (subcomp_f, subcomp_g) ->
                                    let uu____6853 =
                                      let aux t =
                                        let uu____6870 =
                                          let uu____6871 =
                                            let uu____6898 =
                                              let uu____6915 =
                                                let uu____6924 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    ite_t_applied in
                                                FStar_Util.Inr uu____6924 in
                                              (uu____6915,
                                                FStar_Pervasives_Native.None) in
                                            (t, uu____6898,
                                              FStar_Pervasives_Native.None) in
                                          FStar_Syntax_Syntax.Tm_ascribed
                                            uu____6871 in
                                        FStar_Syntax_Syntax.mk uu____6870 r in
                                      let uu____6965 = aux subcomp_f in
                                      let uu____6966 = aux subcomp_g in
                                      (uu____6965, uu____6966) in
                                    (match uu____6853 with
                                     | (tm_subcomp_ascribed_f,
                                        tm_subcomp_ascribed_g) ->
                                         ((let uu____6970 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____6970
                                           then
                                             let uu____6975 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_f in
                                             let uu____6977 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_g in
                                             FStar_Util.print2
                                               "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                               uu____6975 uu____6977
                                           else ());
                                          (let uu____6982 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env tm_subcomp_ascribed_f in
                                           match uu____6982 with
                                           | (uu____6989, uu____6990, g_f) ->
                                               let g_f1 =
                                                 let uu____6993 =
                                                   let uu____6994 =
                                                     let uu____6995 =
                                                       FStar_All.pipe_right
                                                         p_t
                                                         FStar_Syntax_Util.b2t in
                                                     FStar_All.pipe_right
                                                       uu____6995
                                                       (fun uu____6998 ->
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            uu____6998) in
                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                     uu____6994 in
                                                 FStar_TypeChecker_Env.imp_guard
                                                   uu____6993 g_f in
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env g_f1;
                                                (let uu____7000 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env
                                                     tm_subcomp_ascribed_g in
                                                 match uu____7000 with
                                                 | (uu____7007, uu____7008,
                                                    g_g) ->
                                                     let g_g1 =
                                                       let not_p =
                                                         let uu____7012 =
                                                           let uu____7013 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               FStar_Parser_Const.not_lid
                                                               FStar_Syntax_Syntax.delta_constant
                                                               FStar_Pervasives_Native.None in
                                                           FStar_All.pipe_right
                                                             uu____7013
                                                             FStar_Syntax_Syntax.fv_to_tm in
                                                         let uu____7014 =
                                                           let uu____7015 =
                                                             let uu____7024 =
                                                               FStar_All.pipe_right
                                                                 p_t
                                                                 FStar_Syntax_Util.b2t in
                                                             FStar_All.pipe_right
                                                               uu____7024
                                                               FStar_Syntax_Syntax.as_arg in
                                                           [uu____7015] in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____7012
                                                           uu____7014 r in
                                                       let uu____7051 =
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           (FStar_TypeChecker_Common.NonTrivial
                                                              not_p) in
                                                       FStar_TypeChecker_Env.imp_guard
                                                         uu____7051 g_g in
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
                     (let uu____7075 =
                        let uu____7081 =
                          let uu____7083 =
                            FStar_Ident.string_of_lid
                              ed.FStar_Syntax_Syntax.mname in
                          let uu____7085 =
                            FStar_Ident.string_of_lid
                              act.FStar_Syntax_Syntax.action_name in
                          let uu____7087 =
                            FStar_Syntax_Print.binders_to_string "; "
                              act.FStar_Syntax_Syntax.action_params in
                          FStar_Util.format3
                            "Action %s:%s has non-empty action params (%s)"
                            uu____7083 uu____7085 uu____7087 in
                        (FStar_Errors.Fatal_MalformedActionDeclaration,
                          uu____7081) in
                      FStar_Errors.raise_error uu____7075 r)
                   else ();
                   (let uu____7094 =
                      let uu____7099 =
                        FStar_Syntax_Subst.univ_var_opening
                          act.FStar_Syntax_Syntax.action_univs in
                      match uu____7099 with
                      | (usubst, us) ->
                          let uu____7122 =
                            FStar_TypeChecker_Env.push_univ_vars env us in
                          let uu____7123 =
                            let uu___650_7124 = act in
                            let uu____7125 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_defn in
                            let uu____7126 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_typ in
                            {
                              FStar_Syntax_Syntax.action_name =
                                (uu___650_7124.FStar_Syntax_Syntax.action_name);
                              FStar_Syntax_Syntax.action_unqualified_name =
                                (uu___650_7124.FStar_Syntax_Syntax.action_unqualified_name);
                              FStar_Syntax_Syntax.action_univs = us;
                              FStar_Syntax_Syntax.action_params =
                                (uu___650_7124.FStar_Syntax_Syntax.action_params);
                              FStar_Syntax_Syntax.action_defn = uu____7125;
                              FStar_Syntax_Syntax.action_typ = uu____7126
                            } in
                          (uu____7122, uu____7123) in
                    match uu____7094 with
                    | (env1, act1) ->
                        let act_typ =
                          let uu____7130 =
                            let uu____7131 =
                              FStar_Syntax_Subst.compress
                                act1.FStar_Syntax_Syntax.action_typ in
                            uu____7131.FStar_Syntax_Syntax.n in
                          match uu____7130 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                              let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                              let uu____7157 =
                                FStar_Ident.lid_equals
                                  ct.FStar_Syntax_Syntax.effect_name
                                  ed.FStar_Syntax_Syntax.mname in
                              if uu____7157
                              then
                                let repr_ts =
                                  let uu____7161 = repr in
                                  match uu____7161 with
                                  | (us, t, uu____7176) -> (us, t) in
                                let repr1 =
                                  let uu____7194 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      repr_ts
                                      ct.FStar_Syntax_Syntax.comp_univs in
                                  FStar_All.pipe_right uu____7194
                                    FStar_Pervasives_Native.snd in
                                let repr2 =
                                  let uu____7204 =
                                    let uu____7205 =
                                      FStar_Syntax_Syntax.as_arg
                                        ct.FStar_Syntax_Syntax.result_typ in
                                    uu____7205 ::
                                      (ct.FStar_Syntax_Syntax.effect_args) in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____7204 r in
                                let c1 =
                                  let uu____7223 =
                                    let uu____7226 =
                                      FStar_TypeChecker_Env.new_u_univ () in
                                    FStar_Pervasives_Native.Some uu____7226 in
                                  FStar_Syntax_Syntax.mk_Total' repr2
                                    uu____7223 in
                                FStar_Syntax_Util.arrow bs c1
                              else act1.FStar_Syntax_Syntax.action_typ
                          | uu____7229 -> act1.FStar_Syntax_Syntax.action_typ in
                        let uu____7230 =
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                            act_typ in
                        (match uu____7230 with
                         | (act_typ1, uu____7238, g_t) ->
                             let uu____7240 =
                               let uu____7247 =
                                 let uu___675_7248 =
                                   FStar_TypeChecker_Env.set_expected_typ
                                     env1 act_typ1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___675_7248.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___675_7248.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___675_7248.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___675_7248.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___675_7248.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___675_7248.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___675_7248.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___675_7248.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___675_7248.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___675_7248.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     false;
                                   FStar_TypeChecker_Env.effects =
                                     (uu___675_7248.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___675_7248.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___675_7248.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___675_7248.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___675_7248.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___675_7248.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___675_7248.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___675_7248.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___675_7248.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___675_7248.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___675_7248.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___675_7248.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___675_7248.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___675_7248.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___675_7248.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___675_7248.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___675_7248.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___675_7248.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___675_7248.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___675_7248.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___675_7248.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___675_7248.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___675_7248.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___675_7248.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___675_7248.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___675_7248.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___675_7248.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___675_7248.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___675_7248.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___675_7248.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___675_7248.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___675_7248.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___675_7248.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___675_7248.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___675_7248.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___675_7248.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 } in
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 uu____7247
                                 act1.FStar_Syntax_Syntax.action_defn in
                             (match uu____7240 with
                              | (act_defn, uu____7251, g_d) ->
                                  ((let uu____7254 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other
                                           "LayeredEffectsTc") in
                                    if uu____7254
                                    then
                                      let uu____7259 =
                                        FStar_Syntax_Print.term_to_string
                                          act_defn in
                                      let uu____7261 =
                                        FStar_Syntax_Print.term_to_string
                                          act_typ1 in
                                      FStar_Util.print2
                                        "Typechecked action definition: %s and action type: %s\n"
                                        uu____7259 uu____7261
                                    else ());
                                   (let uu____7266 =
                                      let act_typ2 =
                                        FStar_TypeChecker_Normalize.normalize
                                          [FStar_TypeChecker_Env.Beta] env1
                                          act_typ1 in
                                      let uu____7274 =
                                        let uu____7275 =
                                          FStar_Syntax_Subst.compress
                                            act_typ2 in
                                        uu____7275.FStar_Syntax_Syntax.n in
                                      match uu____7274 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____7285) ->
                                          let bs1 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          let env2 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 bs1 in
                                          let uu____7308 =
                                            FStar_Syntax_Util.type_u () in
                                          (match uu____7308 with
                                           | (t, u) ->
                                               let reason =
                                                 let uu____7323 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname in
                                                 let uu____7325 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name in
                                                 FStar_Util.format2
                                                   "implicit for return type of action %s:%s"
                                                   uu____7323 uu____7325 in
                                               let uu____7328 =
                                                 FStar_TypeChecker_Util.new_implicit_var
                                                   reason r env2 t in
                                               (match uu____7328 with
                                                | (a_tm, uu____7348, g_tm) ->
                                                    let uu____7362 =
                                                      fresh_repr r env2 u
                                                        a_tm in
                                                    (match uu____7362 with
                                                     | (repr1, g) ->
                                                         let uu____7375 =
                                                           let uu____7378 =
                                                             let uu____7381 =
                                                               let uu____7384
                                                                 =
                                                                 FStar_TypeChecker_Env.new_u_univ
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 uu____7384
                                                                 (fun
                                                                    uu____7387
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7387) in
                                                             FStar_Syntax_Syntax.mk_Total'
                                                               repr1
                                                               uu____7381 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7378 in
                                                         let uu____7388 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             g g_tm in
                                                         (uu____7375,
                                                           uu____7388))))
                                      | uu____7391 ->
                                          let uu____7392 =
                                            let uu____7398 =
                                              let uu____7400 =
                                                FStar_Ident.string_of_lid
                                                  ed.FStar_Syntax_Syntax.mname in
                                              let uu____7402 =
                                                FStar_Ident.string_of_lid
                                                  act1.FStar_Syntax_Syntax.action_name in
                                              let uu____7404 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.format3
                                                "Unexpected non-function type for action %s:%s (%s)"
                                                uu____7400 uu____7402
                                                uu____7404 in
                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                              uu____7398) in
                                          FStar_Errors.raise_error uu____7392
                                            r in
                                    match uu____7266 with
                                    | (k, g_k) ->
                                        ((let uu____7421 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____7421
                                          then
                                            let uu____7426 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print1
                                              "Expected action type: %s\n"
                                              uu____7426
                                          else ());
                                         (let g =
                                            FStar_TypeChecker_Rel.teq env1
                                              act_typ1 k in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env1) [g_t; g_d; g_k; g];
                                          (let uu____7434 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____7434
                                           then
                                             let uu____7439 =
                                               FStar_Syntax_Print.term_to_string
                                                 k in
                                             FStar_Util.print1
                                               "Expected action type after unification: %s\n"
                                               uu____7439
                                           else ());
                                          (let act_typ2 =
                                             let err_msg t =
                                               let uu____7452 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____7454 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               let uu____7456 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t in
                                               FStar_Util.format3
                                                 "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                 uu____7452 uu____7454
                                                 uu____7456 in
                                             let repr_args t =
                                               let uu____7477 =
                                                 let uu____7478 =
                                                   FStar_Syntax_Subst.compress
                                                     t in
                                                 uu____7478.FStar_Syntax_Syntax.n in
                                               match uu____7477 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (head, a::is) ->
                                                   let uu____7530 =
                                                     let uu____7531 =
                                                       FStar_Syntax_Subst.compress
                                                         head in
                                                     uu____7531.FStar_Syntax_Syntax.n in
                                                   (match uu____7530 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (uu____7540, us) ->
                                                        (us,
                                                          (FStar_Pervasives_Native.fst
                                                             a), is)
                                                    | uu____7550 ->
                                                        let uu____7551 =
                                                          let uu____7557 =
                                                            err_msg t in
                                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                            uu____7557) in
                                                        FStar_Errors.raise_error
                                                          uu____7551 r)
                                               | uu____7566 ->
                                                   let uu____7567 =
                                                     let uu____7573 =
                                                       err_msg t in
                                                     (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                       uu____7573) in
                                                   FStar_Errors.raise_error
                                                     uu____7567 r in
                                             let k1 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.Beta]
                                                 env1 k in
                                             let uu____7583 =
                                               let uu____7584 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____7584.FStar_Syntax_Syntax.n in
                                             match uu____7583 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs, c) ->
                                                 let uu____7609 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c in
                                                 (match uu____7609 with
                                                  | (bs1, c1) ->
                                                      let uu____7616 =
                                                        repr_args
                                                          (FStar_Syntax_Util.comp_result
                                                             c1) in
                                                      (match uu____7616 with
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
                                                           let uu____7627 =
                                                             FStar_Syntax_Syntax.mk_Comp
                                                               ct in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7627))
                                             | uu____7630 ->
                                                 let uu____7631 =
                                                   let uu____7637 =
                                                     err_msg k1 in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____7637) in
                                                 FStar_Errors.raise_error
                                                   uu____7631 r in
                                           (let uu____7641 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env1)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____7641
                                            then
                                              let uu____7646 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.print1
                                                "Action type after injecting it into the monad: %s\n"
                                                uu____7646
                                            else ());
                                           (let act2 =
                                              let uu____7652 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env1 act_defn in
                                              match uu____7652 with
                                              | (us, act_defn1) ->
                                                  if
                                                    act1.FStar_Syntax_Syntax.action_univs
                                                      = []
                                                  then
                                                    let uu___748_7666 = act1 in
                                                    let uu____7667 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        us act_typ2 in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___748_7666.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___748_7666.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = us;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___748_7666.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = act_defn1;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu____7667
                                                    }
                                                  else
                                                    (let uu____7670 =
                                                       ((FStar_List.length us)
                                                          =
                                                          (FStar_List.length
                                                             act1.FStar_Syntax_Syntax.action_univs))
                                                         &&
                                                         (FStar_List.forall2
                                                            (fun u1 ->
                                                               fun u2 ->
                                                                 let uu____7677
                                                                   =
                                                                   FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                 uu____7677 =
                                                                   Prims.int_zero)
                                                            us
                                                            act1.FStar_Syntax_Syntax.action_univs) in
                                                     if uu____7670
                                                     then
                                                       let uu___753_7682 =
                                                         act1 in
                                                       let uu____7683 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           act1.FStar_Syntax_Syntax.action_univs
                                                           act_typ2 in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___753_7682.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___753_7682.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           =
                                                           (uu___753_7682.FStar_Syntax_Syntax.action_univs);
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___753_7682.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7683
                                                       }
                                                     else
                                                       (let uu____7686 =
                                                          let uu____7692 =
                                                            let uu____7694 =
                                                              FStar_Ident.string_of_lid
                                                                ed.FStar_Syntax_Syntax.mname in
                                                            let uu____7696 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____7698 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                us in
                                                            let uu____7700 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                act1.FStar_Syntax_Syntax.action_univs in
                                                            FStar_Util.format4
                                                              "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                              uu____7694
                                                              uu____7696
                                                              uu____7698
                                                              uu____7700 in
                                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                            uu____7692) in
                                                        FStar_Errors.raise_error
                                                          uu____7686 r)) in
                                            act2))))))))) in
                 let tschemes_of uu____7725 =
                   match uu____7725 with | (us, t, ty) -> ((us, t), (us, ty)) in
                 let combinators =
                   let uu____7770 =
                     let uu____7771 = tschemes_of repr in
                     let uu____7776 = tschemes_of return_repr in
                     let uu____7781 = tschemes_of bind_repr in
                     let uu____7786 = tschemes_of stronger_repr in
                     let uu____7791 = tschemes_of if_then_else in
                     {
                       FStar_Syntax_Syntax.l_repr = uu____7771;
                       FStar_Syntax_Syntax.l_return = uu____7776;
                       FStar_Syntax_Syntax.l_bind = uu____7781;
                       FStar_Syntax_Syntax.l_subcomp = uu____7786;
                       FStar_Syntax_Syntax.l_if_then_else = uu____7791
                     } in
                   FStar_Syntax_Syntax.Layered_eff uu____7770 in
                 let uu___762_7796 = ed in
                 let uu____7797 =
                   FStar_List.map (tc_action env0)
                     ed.FStar_Syntax_Syntax.actions in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___762_7796.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___762_7796.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs =
                     (uu___762_7796.FStar_Syntax_Syntax.univs);
                   FStar_Syntax_Syntax.binders =
                     (uu___762_7796.FStar_Syntax_Syntax.binders);
                   FStar_Syntax_Syntax.signature =
                     (let uu____7804 = signature in
                      match uu____7804 with | (us, t, uu____7819) -> (us, t));
                   FStar_Syntax_Syntax.combinators = combinators;
                   FStar_Syntax_Syntax.actions = uu____7797;
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___762_7796.FStar_Syntax_Syntax.eff_attrs)
                 })))))))
let (tc_non_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun _quals ->
        fun _attrs ->
          (let uu____7866 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
               (FStar_Options.Other "ED") in
           if uu____7866
           then
             let uu____7871 = FStar_Syntax_Print.eff_decl_to_string false ed in
             FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____7871
           else ());
          (let uu____7877 =
             let uu____7882 =
               FStar_Syntax_Subst.univ_var_opening
                 ed.FStar_Syntax_Syntax.univs in
             match uu____7882 with
             | (ed_univs_subst, ed_univs) ->
                 let bs =
                   let uu____7906 =
                     FStar_Syntax_Subst.subst_binders ed_univs_subst
                       ed.FStar_Syntax_Syntax.binders in
                   FStar_Syntax_Subst.open_binders uu____7906 in
                 let uu____7907 =
                   let uu____7914 =
                     FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                   FStar_TypeChecker_TcTerm.tc_tparams uu____7914 bs in
                 (match uu____7907 with
                  | (bs1, uu____7920, uu____7921) ->
                      let uu____7922 =
                        let tmp_t =
                          let uu____7932 =
                            let uu____7935 =
                              FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                                (fun uu____7940 ->
                                   FStar_Pervasives_Native.Some uu____7940) in
                            FStar_Syntax_Syntax.mk_Total'
                              FStar_Syntax_Syntax.t_unit uu____7935 in
                          FStar_Syntax_Util.arrow bs1 uu____7932 in
                        let uu____7941 =
                          FStar_TypeChecker_Util.generalize_universes env0
                            tmp_t in
                        match uu____7941 with
                        | (us, tmp_t1) ->
                            let uu____7958 =
                              let uu____7959 =
                                let uu____7960 =
                                  FStar_All.pipe_right tmp_t1
                                    FStar_Syntax_Util.arrow_formals in
                                FStar_All.pipe_right uu____7960
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____7959
                                FStar_Syntax_Subst.close_binders in
                            (us, uu____7958) in
                      (match uu____7922 with
                       | (us, bs2) ->
                           (match ed_univs with
                            | [] -> (us, bs2)
                            | uu____7997 ->
                                let uu____8000 =
                                  ((FStar_List.length ed_univs) =
                                     (FStar_List.length us))
                                    &&
                                    (FStar_List.forall2
                                       (fun u1 ->
                                          fun u2 ->
                                            let uu____8007 =
                                              FStar_Syntax_Syntax.order_univ_name
                                                u1 u2 in
                                            uu____8007 = Prims.int_zero)
                                       ed_univs us) in
                                if uu____8000
                                then (us, bs2)
                                else
                                  (let uu____8018 =
                                     let uu____8024 =
                                       let uu____8026 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____8028 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length ed_univs) in
                                       let uu____8030 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length us) in
                                       FStar_Util.format3
                                         "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                         uu____8026 uu____8028 uu____8030 in
                                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                       uu____8024) in
                                   let uu____8034 =
                                     FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname in
                                   FStar_Errors.raise_error uu____8018
                                     uu____8034)))) in
           match uu____7877 with
           | (us, bs) ->
               let ed1 =
                 let uu___797_8042 = ed in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___797_8042.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___797_8042.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs = us;
                   FStar_Syntax_Syntax.binders = bs;
                   FStar_Syntax_Syntax.signature =
                     (uu___797_8042.FStar_Syntax_Syntax.signature);
                   FStar_Syntax_Syntax.combinators =
                     (uu___797_8042.FStar_Syntax_Syntax.combinators);
                   FStar_Syntax_Syntax.actions =
                     (uu___797_8042.FStar_Syntax_Syntax.actions);
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___797_8042.FStar_Syntax_Syntax.eff_attrs)
                 } in
               let uu____8043 = FStar_Syntax_Subst.univ_var_opening us in
               (match uu____8043 with
                | (ed_univs_subst, ed_univs) ->
                    let uu____8062 =
                      let uu____8067 =
                        FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                      FStar_Syntax_Subst.open_binders' uu____8067 in
                    (match uu____8062 with
                     | (ed_bs, ed_bs_subst) ->
                         let ed2 =
                           let op uu____8088 =
                             match uu____8088 with
                             | (us1, t) ->
                                 let t1 =
                                   let uu____8108 =
                                     FStar_Syntax_Subst.shift_subst
                                       ((FStar_List.length ed_bs) +
                                          (FStar_List.length us1))
                                       ed_univs_subst in
                                   FStar_Syntax_Subst.subst uu____8108 t in
                                 let uu____8117 =
                                   let uu____8118 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length us1) ed_bs_subst in
                                   FStar_Syntax_Subst.subst uu____8118 t1 in
                                 (us1, uu____8117) in
                           let uu___811_8123 = ed1 in
                           let uu____8124 =
                             op ed1.FStar_Syntax_Syntax.signature in
                           let uu____8125 =
                             FStar_Syntax_Util.apply_eff_combinators op
                               ed1.FStar_Syntax_Syntax.combinators in
                           let uu____8126 =
                             FStar_List.map
                               (fun a ->
                                  let uu___814_8134 = a in
                                  let uu____8135 =
                                    let uu____8136 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____8136 in
                                  let uu____8147 =
                                    let uu____8148 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____8148 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      (uu___814_8134.FStar_Syntax_Syntax.action_name);
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (uu___814_8134.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (uu___814_8134.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (uu___814_8134.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____8135;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____8147
                                  }) ed1.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___811_8123.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___811_8123.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs =
                               (uu___811_8123.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders =
                               (uu___811_8123.FStar_Syntax_Syntax.binders);
                             FStar_Syntax_Syntax.signature = uu____8124;
                             FStar_Syntax_Syntax.combinators = uu____8125;
                             FStar_Syntax_Syntax.actions = uu____8126;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___811_8123.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         ((let uu____8160 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____8160
                           then
                             let uu____8165 =
                               FStar_Syntax_Print.eff_decl_to_string false
                                 ed2 in
                             FStar_Util.print1
                               "After typechecking binders eff_decl: \n\t%s\n"
                               uu____8165
                           else ());
                          (let env =
                             let uu____8172 =
                               FStar_TypeChecker_Env.push_univ_vars env0
                                 ed_univs in
                             FStar_TypeChecker_Env.push_binders uu____8172
                               ed_bs in
                           let check_and_gen' comb n env_opt uu____8207 k =
                             match uu____8207 with
                             | (us1, t) ->
                                 let env1 =
                                   if FStar_Util.is_some env_opt
                                   then
                                     FStar_All.pipe_right env_opt
                                       FStar_Util.must
                                   else env in
                                 let uu____8227 =
                                   FStar_Syntax_Subst.open_univ_vars us1 t in
                                 (match uu____8227 with
                                  | (us2, t1) ->
                                      let t2 =
                                        match k with
                                        | FStar_Pervasives_Native.Some k1 ->
                                            let uu____8236 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                              uu____8236 t1 k1
                                        | FStar_Pervasives_Native.None ->
                                            let uu____8237 =
                                              let uu____8244 =
                                                FStar_TypeChecker_Env.push_univ_vars
                                                  env1 us2 in
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                uu____8244 t1 in
                                            (match uu____8237 with
                                             | (t2, uu____8246, g) ->
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env1 g;
                                                  t2)) in
                                      let uu____8249 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env1 t2 in
                                      (match uu____8249 with
                                       | (g_us, t3) ->
                                           (if (FStar_List.length g_us) <> n
                                            then
                                              (let error =
                                                 let uu____8265 =
                                                   FStar_Ident.string_of_lid
                                                     ed2.FStar_Syntax_Syntax.mname in
                                                 let uu____8267 =
                                                   FStar_Util.string_of_int n in
                                                 let uu____8269 =
                                                   let uu____8271 =
                                                     FStar_All.pipe_right
                                                       g_us FStar_List.length in
                                                   FStar_All.pipe_right
                                                     uu____8271
                                                     FStar_Util.string_of_int in
                                                 FStar_Util.format4
                                                   "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                   uu____8265 comb uu____8267
                                                   uu____8269 in
                                               FStar_Errors.raise_error
                                                 (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                   error)
                                                 t3.FStar_Syntax_Syntax.pos)
                                            else ();
                                            (match us2 with
                                             | [] -> (g_us, t3)
                                             | uu____8286 ->
                                                 let uu____8287 =
                                                   ((FStar_List.length us2) =
                                                      (FStar_List.length g_us))
                                                     &&
                                                     (FStar_List.forall2
                                                        (fun u1 ->
                                                           fun u2 ->
                                                             let uu____8294 =
                                                               FStar_Syntax_Syntax.order_univ_name
                                                                 u1 u2 in
                                                             uu____8294 =
                                                               Prims.int_zero)
                                                        us2 g_us) in
                                                 if uu____8287
                                                 then (g_us, t3)
                                                 else
                                                   (let uu____8305 =
                                                      let uu____8311 =
                                                        let uu____8313 =
                                                          FStar_Ident.string_of_lid
                                                            ed2.FStar_Syntax_Syntax.mname in
                                                        let uu____8315 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               us2) in
                                                        let uu____8317 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               g_us) in
                                                        FStar_Util.format4
                                                          "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                          uu____8313 comb
                                                          uu____8315
                                                          uu____8317 in
                                                      (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                        uu____8311) in
                                                    FStar_Errors.raise_error
                                                      uu____8305
                                                      t3.FStar_Syntax_Syntax.pos))))) in
                           let signature =
                             check_and_gen' "signature" Prims.int_one
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature
                               FStar_Pervasives_Native.None in
                           (let uu____8325 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "ED") in
                            if uu____8325
                            then
                              let uu____8330 =
                                FStar_Syntax_Print.tscheme_to_string
                                  signature in
                              FStar_Util.print1 "Typechecked signature: %s\n"
                                uu____8330
                            else ());
                           (let fresh_a_and_wp uu____8346 =
                              let fail t =
                                let uu____8359 =
                                  FStar_TypeChecker_Err.unexpected_signature_for_monad
                                    env ed2.FStar_Syntax_Syntax.mname t in
                                FStar_Errors.raise_error uu____8359
                                  (FStar_Pervasives_Native.snd
                                     ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                              let uu____8375 =
                                FStar_TypeChecker_Env.inst_tscheme signature in
                              match uu____8375 with
                              | (uu____8386, signature1) ->
                                  let uu____8388 =
                                    let uu____8389 =
                                      FStar_Syntax_Subst.compress signature1 in
                                    uu____8389.FStar_Syntax_Syntax.n in
                                  (match uu____8388 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs1, uu____8399) ->
                                       let bs2 =
                                         FStar_Syntax_Subst.open_binders bs1 in
                                       (match bs2 with
                                        | (a, uu____8428)::(wp, uu____8430)::[]
                                            ->
                                            (a,
                                              (wp.FStar_Syntax_Syntax.sort))
                                        | uu____8459 -> fail signature1)
                                   | uu____8460 -> fail signature1) in
                            let log_combinator s ts =
                              let uu____8474 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "ED") in
                              if uu____8474
                              then
                                let uu____8479 =
                                  FStar_Ident.string_of_lid
                                    ed2.FStar_Syntax_Syntax.mname in
                                let uu____8481 =
                                  FStar_Syntax_Print.tscheme_to_string ts in
                                FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                  uu____8479 s uu____8481
                              else () in
                            let ret_wp =
                              let uu____8487 = fresh_a_and_wp () in
                              match uu____8487 with
                              | (a, wp_sort) ->
                                  let k =
                                    let uu____8503 =
                                      let uu____8512 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____8519 =
                                        let uu____8528 =
                                          let uu____8535 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____8535 in
                                        [uu____8528] in
                                      uu____8512 :: uu____8519 in
                                    let uu____8554 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                    FStar_Syntax_Util.arrow uu____8503
                                      uu____8554 in
                                  let uu____8557 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_return_vc_combinator in
                                  check_and_gen' "ret_wp" Prims.int_one
                                    FStar_Pervasives_Native.None uu____8557
                                    (FStar_Pervasives_Native.Some k) in
                            log_combinator "ret_wp" ret_wp;
                            (let bind_wp =
                               let uu____8571 = fresh_a_and_wp () in
                               match uu____8571 with
                               | (a, wp_sort_a) ->
                                   let uu____8584 = fresh_a_and_wp () in
                                   (match uu____8584 with
                                    | (b, wp_sort_b) ->
                                        let wp_sort_a_b =
                                          let uu____8600 =
                                            let uu____8609 =
                                              let uu____8616 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____8616 in
                                            [uu____8609] in
                                          let uu____8629 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8600
                                            uu____8629 in
                                        let k =
                                          let uu____8635 =
                                            let uu____8644 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_range in
                                            let uu____8651 =
                                              let uu____8660 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu____8667 =
                                                let uu____8676 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b in
                                                let uu____8683 =
                                                  let uu____8692 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu____8699 =
                                                    let uu____8708 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a_b in
                                                    [uu____8708] in
                                                  uu____8692 :: uu____8699 in
                                                uu____8676 :: uu____8683 in
                                              uu____8660 :: uu____8667 in
                                            uu____8644 :: uu____8651 in
                                          let uu____8751 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8635
                                            uu____8751 in
                                        let uu____8754 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_bind_vc_combinator in
                                        check_and_gen' "bind_wp"
                                          (Prims.of_int (2))
                                          FStar_Pervasives_Native.None
                                          uu____8754
                                          (FStar_Pervasives_Native.Some k)) in
                             log_combinator "bind_wp" bind_wp;
                             (let stronger =
                                let uu____8768 = fresh_a_and_wp () in
                                match uu____8768 with
                                | (a, wp_sort_a) ->
                                    let uu____8781 =
                                      FStar_Syntax_Util.type_u () in
                                    (match uu____8781 with
                                     | (t, uu____8787) ->
                                         let k =
                                           let uu____8791 =
                                             let uu____8800 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a in
                                             let uu____8807 =
                                               let uu____8816 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               let uu____8823 =
                                                 let uu____8832 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____8832] in
                                               uu____8816 :: uu____8823 in
                                             uu____8800 :: uu____8807 in
                                           let uu____8863 =
                                             FStar_Syntax_Syntax.mk_Total t in
                                           FStar_Syntax_Util.arrow uu____8791
                                             uu____8863 in
                                         let uu____8866 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_stronger_vc_combinator in
                                         check_and_gen' "stronger"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           uu____8866
                                           (FStar_Pervasives_Native.Some k)) in
                              log_combinator "stronger" stronger;
                              (let if_then_else =
                                 let uu____8880 = fresh_a_and_wp () in
                                 match uu____8880 with
                                 | (a, wp_sort_a) ->
                                     let p =
                                       let uu____8894 =
                                         let uu____8897 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____8897 in
                                       let uu____8898 =
                                         let uu____8899 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____8899
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____8894
                                         uu____8898 in
                                     let k =
                                       let uu____8911 =
                                         let uu____8920 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____8927 =
                                           let uu____8936 =
                                             FStar_Syntax_Syntax.mk_binder p in
                                           let uu____8943 =
                                             let uu____8952 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____8959 =
                                               let uu____8968 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____8968] in
                                             uu____8952 :: uu____8959 in
                                           uu____8936 :: uu____8943 in
                                         uu____8920 :: uu____8927 in
                                       let uu____9005 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____8911
                                         uu____9005 in
                                     let uu____9008 =
                                       let uu____9013 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                       FStar_All.pipe_right uu____9013
                                         FStar_Util.must in
                                     check_and_gen' "if_then_else"
                                       Prims.int_one
                                       FStar_Pervasives_Native.None
                                       uu____9008
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "if_then_else" if_then_else;
                               (let ite_wp =
                                  let uu____9045 = fresh_a_and_wp () in
                                  match uu____9045 with
                                  | (a, wp_sort_a) ->
                                      let k =
                                        let uu____9061 =
                                          let uu____9070 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____9077 =
                                            let uu____9086 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a in
                                            [uu____9086] in
                                          uu____9070 :: uu____9077 in
                                        let uu____9111 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_a in
                                        FStar_Syntax_Util.arrow uu____9061
                                          uu____9111 in
                                      let uu____9114 =
                                        let uu____9119 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_wp_ite_combinator in
                                        FStar_All.pipe_right uu____9119
                                          FStar_Util.must in
                                      check_and_gen' "ite_wp" Prims.int_one
                                        FStar_Pervasives_Native.None
                                        uu____9114
                                        (FStar_Pervasives_Native.Some k) in
                                log_combinator "ite_wp" ite_wp;
                                (let close_wp =
                                   let uu____9135 = fresh_a_and_wp () in
                                   match uu____9135 with
                                   | (a, wp_sort_a) ->
                                       let b =
                                         let uu____9149 =
                                           let uu____9152 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname in
                                           FStar_Pervasives_Native.Some
                                             uu____9152 in
                                         let uu____9153 =
                                           let uu____9154 =
                                             FStar_Syntax_Util.type_u () in
                                           FStar_All.pipe_right uu____9154
                                             FStar_Pervasives_Native.fst in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____9149 uu____9153 in
                                       let wp_sort_b_a =
                                         let uu____9166 =
                                           let uu____9175 =
                                             let uu____9182 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 b in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____9182 in
                                           [uu____9175] in
                                         let uu____9195 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____9166
                                           uu____9195 in
                                       let k =
                                         let uu____9201 =
                                           let uu____9210 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____9217 =
                                             let uu____9226 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____9233 =
                                               let uu____9242 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_b_a in
                                               [uu____9242] in
                                             uu____9226 :: uu____9233 in
                                           uu____9210 :: uu____9217 in
                                         let uu____9273 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____9201
                                           uu____9273 in
                                       let uu____9276 =
                                         let uu____9281 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_wp_close_combinator in
                                         FStar_All.pipe_right uu____9281
                                           FStar_Util.must in
                                       check_and_gen' "close_wp"
                                         (Prims.of_int (2))
                                         FStar_Pervasives_Native.None
                                         uu____9276
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "close_wp" close_wp;
                                 (let trivial =
                                    let uu____9297 = fresh_a_and_wp () in
                                    match uu____9297 with
                                    | (a, wp_sort_a) ->
                                        let uu____9310 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____9310 with
                                         | (t, uu____9316) ->
                                             let k =
                                               let uu____9320 =
                                                 let uu____9329 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a in
                                                 let uu____9336 =
                                                   let uu____9345 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a in
                                                   [uu____9345] in
                                                 uu____9329 :: uu____9336 in
                                               let uu____9370 =
                                                 FStar_Syntax_Syntax.mk_GTotal
                                                   t in
                                               FStar_Syntax_Util.arrow
                                                 uu____9320 uu____9370 in
                                             let trivial =
                                               let uu____9374 =
                                                 let uu____9379 =
                                                   FStar_All.pipe_right ed2
                                                     FStar_Syntax_Util.get_wp_trivial_combinator in
                                                 FStar_All.pipe_right
                                                   uu____9379 FStar_Util.must in
                                               check_and_gen' "trivial"
                                                 Prims.int_one
                                                 FStar_Pervasives_Native.None
                                                 uu____9374
                                                 (FStar_Pervasives_Native.Some
                                                    k) in
                                             (log_combinator "trivial"
                                                trivial;
                                              trivial)) in
                                  let uu____9394 =
                                    let uu____9411 =
                                      FStar_All.pipe_right ed2
                                        FStar_Syntax_Util.get_eff_repr in
                                    match uu____9411 with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          (ed2.FStar_Syntax_Syntax.actions))
                                    | uu____9440 ->
                                        let repr =
                                          let uu____9444 = fresh_a_and_wp () in
                                          match uu____9444 with
                                          | (a, wp_sort_a) ->
                                              let uu____9457 =
                                                FStar_Syntax_Util.type_u () in
                                              (match uu____9457 with
                                               | (t, uu____9463) ->
                                                   let k =
                                                     let uu____9467 =
                                                       let uu____9476 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a in
                                                       let uu____9483 =
                                                         let uu____9492 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             wp_sort_a in
                                                         [uu____9492] in
                                                       uu____9476 ::
                                                         uu____9483 in
                                                     let uu____9517 =
                                                       FStar_Syntax_Syntax.mk_GTotal
                                                         t in
                                                     FStar_Syntax_Util.arrow
                                                       uu____9467 uu____9517 in
                                                   let uu____9520 =
                                                     let uu____9525 =
                                                       FStar_All.pipe_right
                                                         ed2
                                                         FStar_Syntax_Util.get_eff_repr in
                                                     FStar_All.pipe_right
                                                       uu____9525
                                                       FStar_Util.must in
                                                   check_and_gen' "repr"
                                                     Prims.int_one
                                                     FStar_Pervasives_Native.None
                                                     uu____9520
                                                     (FStar_Pervasives_Native.Some
                                                        k)) in
                                        (log_combinator "repr" repr;
                                         (let mk_repr' t wp =
                                            let uu____9569 =
                                              FStar_TypeChecker_Env.inst_tscheme
                                                repr in
                                            match uu____9569 with
                                            | (uu____9576, repr1) ->
                                                let repr2 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.EraseUniverses;
                                                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                    env repr1 in
                                                let uu____9579 =
                                                  let uu____9580 =
                                                    let uu____9597 =
                                                      let uu____9608 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9625 =
                                                        let uu____9636 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9636] in
                                                      uu____9608 ::
                                                        uu____9625 in
                                                    (repr2, uu____9597) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9580 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9579
                                                  FStar_Range.dummyRange in
                                          let mk_repr a wp =
                                            let uu____9702 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            mk_repr' uu____9702 wp in
                                          let destruct_repr t =
                                            let uu____9717 =
                                              let uu____9718 =
                                                FStar_Syntax_Subst.compress t in
                                              uu____9718.FStar_Syntax_Syntax.n in
                                            match uu____9717 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____9729,
                                                 (t1, uu____9731)::(wp,
                                                                    uu____9733)::[])
                                                -> (t1, wp)
                                            | uu____9792 ->
                                                failwith
                                                  "Unexpected repr type" in
                                          let return_repr =
                                            let return_repr_ts =
                                              let uu____9808 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_return_repr in
                                              FStar_All.pipe_right uu____9808
                                                FStar_Util.must in
                                            let uu____9835 =
                                              fresh_a_and_wp () in
                                            match uu____9835 with
                                            | (a, uu____9843) ->
                                                let x_a =
                                                  let uu____9849 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____9849 in
                                                let res =
                                                  let wp =
                                                    let uu____9855 =
                                                      let uu____9856 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp in
                                                      FStar_All.pipe_right
                                                        uu____9856
                                                        FStar_Pervasives_Native.snd in
                                                    let uu____9865 =
                                                      let uu____9866 =
                                                        let uu____9875 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_All.pipe_right
                                                          uu____9875
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9884 =
                                                        let uu____9895 =
                                                          let uu____9904 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____9904
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9895] in
                                                      uu____9866 ::
                                                        uu____9884 in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____9855 uu____9865
                                                      FStar_Range.dummyRange in
                                                  mk_repr a wp in
                                                let k =
                                                  let uu____9940 =
                                                    let uu____9949 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a in
                                                    let uu____9956 =
                                                      let uu____9965 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          x_a in
                                                      [uu____9965] in
                                                    uu____9949 :: uu____9956 in
                                                  let uu____9990 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res in
                                                  FStar_Syntax_Util.arrow
                                                    uu____9940 uu____9990 in
                                                let uu____9993 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env k in
                                                (match uu____9993 with
                                                 | (k1, uu____10001,
                                                    uu____10002) ->
                                                     let env1 =
                                                       let uu____10006 =
                                                         FStar_TypeChecker_Env.set_range
                                                           env
                                                           (FStar_Pervasives_Native.snd
                                                              return_repr_ts).FStar_Syntax_Syntax.pos in
                                                       FStar_Pervasives_Native.Some
                                                         uu____10006 in
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
                                               let uu____10019 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_bind_repr in
                                               FStar_All.pipe_right
                                                 uu____10019 FStar_Util.must in
                                             let r =
                                               let uu____10057 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_0
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_All.pipe_right
                                                 uu____10057
                                                 FStar_Syntax_Syntax.fv_to_tm in
                                             let uu____10058 =
                                               fresh_a_and_wp () in
                                             match uu____10058 with
                                             | (a, wp_sort_a) ->
                                                 let uu____10071 =
                                                   fresh_a_and_wp () in
                                                 (match uu____10071 with
                                                  | (b, wp_sort_b) ->
                                                      let wp_sort_a_b =
                                                        let uu____10087 =
                                                          let uu____10096 =
                                                            let uu____10103 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____10103 in
                                                          [uu____10096] in
                                                        let uu____10116 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            wp_sort_b in
                                                        FStar_Syntax_Util.arrow
                                                          uu____10087
                                                          uu____10116 in
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
                                                        let uu____10124 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "x_a"
                                                          FStar_Pervasives_Native.None
                                                          uu____10124 in
                                                      let wp_g_x =
                                                        let uu____10127 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g in
                                                        let uu____10128 =
                                                          let uu____10129 =
                                                            let uu____10138 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a in
                                                            FStar_All.pipe_right
                                                              uu____10138
                                                              FStar_Syntax_Syntax.as_arg in
                                                          [uu____10129] in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____10127
                                                          uu____10128
                                                          FStar_Range.dummyRange in
                                                      let res =
                                                        let wp =
                                                          let uu____10167 =
                                                            let uu____10168 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp in
                                                            FStar_All.pipe_right
                                                              uu____10168
                                                              FStar_Pervasives_Native.snd in
                                                          let uu____10177 =
                                                            let uu____10178 =
                                                              let uu____10181
                                                                =
                                                                let uu____10184
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                let uu____10185
                                                                  =
                                                                  let uu____10188
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                  let uu____10189
                                                                    =
                                                                    let uu____10192
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu____10193
                                                                    =
                                                                    let uu____10196
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____10196] in
                                                                    uu____10192
                                                                    ::
                                                                    uu____10193 in
                                                                  uu____10188
                                                                    ::
                                                                    uu____10189 in
                                                                uu____10184
                                                                  ::
                                                                  uu____10185 in
                                                              r ::
                                                                uu____10181 in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10178 in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____10167
                                                            uu____10177
                                                            FStar_Range.dummyRange in
                                                        mk_repr b wp in
                                                      let maybe_range_arg =
                                                        let uu____10214 =
                                                          FStar_Util.for_some
                                                            (FStar_Syntax_Util.attr_eq
                                                               FStar_Syntax_Util.dm4f_bind_range_attr)
                                                            ed2.FStar_Syntax_Syntax.eff_attrs in
                                                        if uu____10214
                                                        then
                                                          let uu____10225 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          let uu____10232 =
                                                            let uu____10241 =
                                                              FStar_Syntax_Syntax.null_binder
                                                                FStar_Syntax_Syntax.t_range in
                                                            [uu____10241] in
                                                          uu____10225 ::
                                                            uu____10232
                                                        else [] in
                                                      let k =
                                                        let uu____10277 =
                                                          let uu____10286 =
                                                            let uu____10295 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu____10302 =
                                                              let uu____10311
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  b in
                                                              [uu____10311] in
                                                            uu____10295 ::
                                                              uu____10302 in
                                                          let uu____10336 =
                                                            let uu____10345 =
                                                              let uu____10354
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  wp_f in
                                                              let uu____10361
                                                                =
                                                                let uu____10370
                                                                  =
                                                                  let uu____10377
                                                                    =
                                                                    let uu____10378
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu____10378 in
                                                                  FStar_Syntax_Syntax.null_binder
                                                                    uu____10377 in
                                                                let uu____10379
                                                                  =
                                                                  let uu____10388
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                  let uu____10395
                                                                    =
                                                                    let uu____10404
                                                                    =
                                                                    let uu____10411
                                                                    =
                                                                    let uu____10412
                                                                    =
                                                                    let uu____10421
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____10421] in
                                                                    let uu____10440
                                                                    =
                                                                    let uu____10443
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____10443 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____10412
                                                                    uu____10440 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____10411 in
                                                                    [uu____10404] in
                                                                  uu____10388
                                                                    ::
                                                                    uu____10395 in
                                                                uu____10370
                                                                  ::
                                                                  uu____10379 in
                                                              uu____10354 ::
                                                                uu____10361 in
                                                            FStar_List.append
                                                              maybe_range_arg
                                                              uu____10345 in
                                                          FStar_List.append
                                                            uu____10286
                                                            uu____10336 in
                                                        let uu____10488 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            res in
                                                        FStar_Syntax_Util.arrow
                                                          uu____10277
                                                          uu____10488 in
                                                      let uu____10491 =
                                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                          env k in
                                                      (match uu____10491 with
                                                       | (k1, uu____10499,
                                                          uu____10500) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.set_range
                                                               env
                                                               (FStar_Pervasives_Native.snd
                                                                  bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                           let env2 =
                                                             FStar_All.pipe_right
                                                               (let uu___1009_10510
                                                                  = env1 in
                                                                {
                                                                  FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.solver);
                                                                  FStar_TypeChecker_Env.range
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.range);
                                                                  FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.curmodule);
                                                                  FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.gamma);
                                                                  FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.gamma_sig);
                                                                  FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.gamma_cache);
                                                                  FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.modules);
                                                                  FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.expected_typ);
                                                                  FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.sigtab);
                                                                  FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.attrtab);
                                                                  FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.instantiate_imp);
                                                                  FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.effects);
                                                                  FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.generalize);
                                                                  FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.letrecs);
                                                                  FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.top_level);
                                                                  FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.check_uvars);
                                                                  FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.use_eq);
                                                                  FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.use_eq_strict);
                                                                  FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.is_iface);
                                                                  FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.admit);
                                                                  FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                  FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.lax_universes);
                                                                  FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.phase1);
                                                                  FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.failhard);
                                                                  FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.nosynth);
                                                                  FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.uvar_subtyping);
                                                                  FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.tc_term);
                                                                  FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.type_of);
                                                                  FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.universe_of);
                                                                  FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.check_type_of);
                                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.use_bv_sorts);
                                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                  FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.normalized_eff_names);
                                                                  FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.fv_delta_depths);
                                                                  FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.proof_ns);
                                                                  FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.synth_hook);
                                                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                  FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.splice);
                                                                  FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.mpreprocess);
                                                                  FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.postprocess);
                                                                  FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.identifier_info);
                                                                  FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.tc_hooks);
                                                                  FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.dsenv);
                                                                  FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.nbe);
                                                                  FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.strict_args_tab);
                                                                  FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.erasable_types_tab);
                                                                  FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (
                                                                    uu___1009_10510.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                })
                                                               (fun
                                                                  uu____10512
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____10512) in
                                                           check_and_gen'
                                                             "bind_repr"
                                                             (Prims.of_int (2))
                                                             env2
                                                             bind_repr_ts
                                                             (FStar_Pervasives_Native.Some
                                                                k1))) in
                                           log_combinator "bind_repr"
                                             bind_repr;
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
                                                (let uu____10539 =
                                                   if
                                                     act.FStar_Syntax_Syntax.action_univs
                                                       = []
                                                   then (env, act)
                                                   else
                                                     (let uu____10553 =
                                                        FStar_Syntax_Subst.univ_var_opening
                                                          act.FStar_Syntax_Syntax.action_univs in
                                                      match uu____10553 with
                                                      | (usubst, uvs) ->
                                                          let uu____10576 =
                                                            FStar_TypeChecker_Env.push_univ_vars
                                                              env uvs in
                                                          let uu____10577 =
                                                            let uu___1022_10578
                                                              = act in
                                                            let uu____10579 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_defn in
                                                            let uu____10580 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_typ in
                                                            {
                                                              FStar_Syntax_Syntax.action_name
                                                                =
                                                                (uu___1022_10578.FStar_Syntax_Syntax.action_name);
                                                              FStar_Syntax_Syntax.action_unqualified_name
                                                                =
                                                                (uu___1022_10578.FStar_Syntax_Syntax.action_unqualified_name);
                                                              FStar_Syntax_Syntax.action_univs
                                                                = uvs;
                                                              FStar_Syntax_Syntax.action_params
                                                                =
                                                                (uu___1022_10578.FStar_Syntax_Syntax.action_params);
                                                              FStar_Syntax_Syntax.action_defn
                                                                = uu____10579;
                                                              FStar_Syntax_Syntax.action_typ
                                                                = uu____10580
                                                            } in
                                                          (uu____10576,
                                                            uu____10577)) in
                                                 match uu____10539 with
                                                 | (env1, act1) ->
                                                     let act_typ =
                                                       let uu____10584 =
                                                         let uu____10585 =
                                                           FStar_Syntax_Subst.compress
                                                             act1.FStar_Syntax_Syntax.action_typ in
                                                         uu____10585.FStar_Syntax_Syntax.n in
                                                       match uu____10584 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let c1 =
                                                             FStar_Syntax_Util.comp_to_comp_typ
                                                               c in
                                                           let uu____10611 =
                                                             FStar_Ident.lid_equals
                                                               c1.FStar_Syntax_Syntax.effect_name
                                                               ed2.FStar_Syntax_Syntax.mname in
                                                           if uu____10611
                                                           then
                                                             let uu____10614
                                                               =
                                                               let uu____10617
                                                                 =
                                                                 let uu____10618
                                                                   =
                                                                   let uu____10619
                                                                    =
                                                                    FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                   FStar_Pervasives_Native.fst
                                                                    uu____10619 in
                                                                 mk_repr'
                                                                   c1.FStar_Syntax_Syntax.result_typ
                                                                   uu____10618 in
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 uu____10617 in
                                                             FStar_Syntax_Util.arrow
                                                               bs1
                                                               uu____10614
                                                           else
                                                             act1.FStar_Syntax_Syntax.action_typ
                                                       | uu____10642 ->
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                     let uu____10643 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env1 act_typ in
                                                     (match uu____10643 with
                                                      | (act_typ1,
                                                         uu____10651, g_t) ->
                                                          let env' =
                                                            let uu___1039_10654
                                                              =
                                                              FStar_TypeChecker_Env.set_expected_typ
                                                                env1 act_typ1 in
                                                            {
                                                              FStar_TypeChecker_Env.solver
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.solver);
                                                              FStar_TypeChecker_Env.range
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.range);
                                                              FStar_TypeChecker_Env.curmodule
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.curmodule);
                                                              FStar_TypeChecker_Env.gamma
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.gamma);
                                                              FStar_TypeChecker_Env.gamma_sig
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.gamma_sig);
                                                              FStar_TypeChecker_Env.gamma_cache
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.gamma_cache);
                                                              FStar_TypeChecker_Env.modules
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.modules);
                                                              FStar_TypeChecker_Env.expected_typ
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.expected_typ);
                                                              FStar_TypeChecker_Env.sigtab
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.sigtab);
                                                              FStar_TypeChecker_Env.attrtab
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.attrtab);
                                                              FStar_TypeChecker_Env.instantiate_imp
                                                                = false;
                                                              FStar_TypeChecker_Env.effects
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.effects);
                                                              FStar_TypeChecker_Env.generalize
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.generalize);
                                                              FStar_TypeChecker_Env.letrecs
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.letrecs);
                                                              FStar_TypeChecker_Env.top_level
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.top_level);
                                                              FStar_TypeChecker_Env.check_uvars
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.check_uvars);
                                                              FStar_TypeChecker_Env.use_eq
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.use_eq);
                                                              FStar_TypeChecker_Env.use_eq_strict
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.use_eq_strict);
                                                              FStar_TypeChecker_Env.is_iface
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.is_iface);
                                                              FStar_TypeChecker_Env.admit
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.admit);
                                                              FStar_TypeChecker_Env.lax
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.lax);
                                                              FStar_TypeChecker_Env.lax_universes
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.lax_universes);
                                                              FStar_TypeChecker_Env.phase1
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.phase1);
                                                              FStar_TypeChecker_Env.failhard
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.failhard);
                                                              FStar_TypeChecker_Env.nosynth
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.nosynth);
                                                              FStar_TypeChecker_Env.uvar_subtyping
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.uvar_subtyping);
                                                              FStar_TypeChecker_Env.tc_term
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.tc_term);
                                                              FStar_TypeChecker_Env.type_of
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.type_of);
                                                              FStar_TypeChecker_Env.universe_of
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.universe_of);
                                                              FStar_TypeChecker_Env.check_type_of
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.check_type_of);
                                                              FStar_TypeChecker_Env.use_bv_sorts
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.use_bv_sorts);
                                                              FStar_TypeChecker_Env.qtbl_name_and_index
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                              FStar_TypeChecker_Env.normalized_eff_names
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.normalized_eff_names);
                                                              FStar_TypeChecker_Env.fv_delta_depths
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.fv_delta_depths);
                                                              FStar_TypeChecker_Env.proof_ns
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.proof_ns);
                                                              FStar_TypeChecker_Env.synth_hook
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.synth_hook);
                                                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                              FStar_TypeChecker_Env.splice
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.splice);
                                                              FStar_TypeChecker_Env.mpreprocess
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.mpreprocess);
                                                              FStar_TypeChecker_Env.postprocess
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.postprocess);
                                                              FStar_TypeChecker_Env.identifier_info
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.identifier_info);
                                                              FStar_TypeChecker_Env.tc_hooks
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.tc_hooks);
                                                              FStar_TypeChecker_Env.dsenv
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.dsenv);
                                                              FStar_TypeChecker_Env.nbe
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.nbe);
                                                              FStar_TypeChecker_Env.strict_args_tab
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.strict_args_tab);
                                                              FStar_TypeChecker_Env.erasable_types_tab
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.erasable_types_tab);
                                                              FStar_TypeChecker_Env.enable_defer_to_tac
                                                                =
                                                                (uu___1039_10654.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                            } in
                                                          ((let uu____10657 =
                                                              FStar_TypeChecker_Env.debug
                                                                env1
                                                                (FStar_Options.Other
                                                                   "ED") in
                                                            if uu____10657
                                                            then
                                                              let uu____10661
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  act1.FStar_Syntax_Syntax.action_name in
                                                              let uu____10663
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act1.FStar_Syntax_Syntax.action_defn in
                                                              let uu____10665
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ1 in
                                                              FStar_Util.print3
                                                                "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                uu____10661
                                                                uu____10663
                                                                uu____10665
                                                            else ());
                                                           (let uu____10670 =
                                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                env'
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            match uu____10670
                                                            with
                                                            | (act_defn,
                                                               uu____10678,
                                                               g_a) ->
                                                                let act_defn1
                                                                  =
                                                                  FStar_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant]
                                                                    env1
                                                                    act_defn in
                                                                let act_typ2
                                                                  =
                                                                  FStar_TypeChecker_Normalize.normalize
                                                                    [
                                                                    FStar_TypeChecker_Env.UnfoldUntil
                                                                    FStar_Syntax_Syntax.delta_constant;
                                                                    FStar_TypeChecker_Env.Eager_unfolding;
                                                                    FStar_TypeChecker_Env.Beta]
                                                                    env1
                                                                    act_typ1 in
                                                                let uu____10682
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
                                                                    let uu____10718
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10718
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10730)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10737
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10737 in
                                                                    let uu____10740
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10740
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10754,
                                                                    g) ->
                                                                    (k1, g)))
                                                                  | uu____10758
                                                                    ->
                                                                    let uu____10759
                                                                    =
                                                                    let uu____10765
                                                                    =
                                                                    let uu____10767
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10769
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10767
                                                                    uu____10769 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10765) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10759
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                (match uu____10682
                                                                 with
                                                                 | (expected_k,
                                                                    g_k) ->
                                                                    let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    ((
                                                                    let uu____10787
                                                                    =
                                                                    let uu____10788
                                                                    =
                                                                    let uu____10789
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10789 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10788 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10787);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu____10791
                                                                    =
                                                                    let uu____10792
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10792.FStar_Syntax_Syntax.n in
                                                                    match uu____10791
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10817
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10817
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10824
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10824
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10844
                                                                    =
                                                                    let uu____10845
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10845] in
                                                                    let uu____10846
                                                                    =
                                                                    let uu____10857
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10857] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10844;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10846;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10882
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10882))
                                                                    | 
                                                                    uu____10885
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10887
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10909
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10909)) in
                                                                    match uu____10887
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
                                                                    let uu___1089_10928
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1089_10928.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1089_10928.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1089_10928.FStar_Syntax_Syntax.action_params);
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
                                            ((FStar_Pervasives_Native.Some
                                                repr),
                                              (FStar_Pervasives_Native.Some
                                                 return_repr),
                                              (FStar_Pervasives_Native.Some
                                                 bind_repr), actions))))) in
                                  match uu____9394 with
                                  | (repr, return_repr, bind_repr, actions)
                                      ->
                                      let cl ts =
                                        let ts1 =
                                          FStar_Syntax_Subst.close_tscheme
                                            ed_bs ts in
                                        let ed_univs_closing =
                                          FStar_Syntax_Subst.univ_var_closing
                                            ed_univs in
                                        let uu____10971 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length ed_bs)
                                            ed_univs_closing in
                                        FStar_Syntax_Subst.subst_tscheme
                                          uu____10971 ts1 in
                                      let combinators =
                                        {
                                          FStar_Syntax_Syntax.ret_wp = ret_wp;
                                          FStar_Syntax_Syntax.bind_wp =
                                            bind_wp;
                                          FStar_Syntax_Syntax.stronger =
                                            stronger;
                                          FStar_Syntax_Syntax.if_then_else =
                                            if_then_else;
                                          FStar_Syntax_Syntax.ite_wp = ite_wp;
                                          FStar_Syntax_Syntax.close_wp =
                                            close_wp;
                                          FStar_Syntax_Syntax.trivial =
                                            trivial;
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
                                            uu____10983 ->
                                            FStar_Syntax_Syntax.Primitive_eff
                                              combinators1
                                        | FStar_Syntax_Syntax.DM4F_eff
                                            uu____10984 ->
                                            FStar_Syntax_Syntax.DM4F_eff
                                              combinators1
                                        | uu____10985 ->
                                            failwith
                                              "Impossible! tc_eff_decl on a layered effect is not expected" in
                                      let ed3 =
                                        let uu___1109_10988 = ed2 in
                                        let uu____10989 = cl signature in
                                        let uu____10990 =
                                          FStar_List.map
                                            (fun a ->
                                               let uu___1112_10998 = a in
                                               let uu____10999 =
                                                 let uu____11000 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_defn)) in
                                                 FStar_All.pipe_right
                                                   uu____11000
                                                   FStar_Pervasives_Native.snd in
                                               let uu____11025 =
                                                 let uu____11026 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_typ)) in
                                                 FStar_All.pipe_right
                                                   uu____11026
                                                   FStar_Pervasives_Native.snd in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___1112_10998.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___1112_10998.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   =
                                                   (uu___1112_10998.FStar_Syntax_Syntax.action_univs);
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___1112_10998.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = uu____10999;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____11025
                                               }) actions in
                                        {
                                          FStar_Syntax_Syntax.mname =
                                            (uu___1109_10988.FStar_Syntax_Syntax.mname);
                                          FStar_Syntax_Syntax.cattributes =
                                            (uu___1109_10988.FStar_Syntax_Syntax.cattributes);
                                          FStar_Syntax_Syntax.univs =
                                            (uu___1109_10988.FStar_Syntax_Syntax.univs);
                                          FStar_Syntax_Syntax.binders =
                                            (uu___1109_10988.FStar_Syntax_Syntax.binders);
                                          FStar_Syntax_Syntax.signature =
                                            uu____10989;
                                          FStar_Syntax_Syntax.combinators =
                                            combinators2;
                                          FStar_Syntax_Syntax.actions =
                                            uu____10990;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            (uu___1109_10988.FStar_Syntax_Syntax.eff_attrs)
                                        } in
                                      ((let uu____11052 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "ED") in
                                        if uu____11052
                                        then
                                          let uu____11057 =
                                            FStar_Syntax_Print.eff_decl_to_string
                                              false ed3 in
                                          FStar_Util.print1
                                            "Typechecked effect declaration:\n\t%s\n"
                                            uu____11057
                                        else ());
                                       ed3)))))))))))))
let (tc_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.attribute Prims.list ->
          FStar_Syntax_Syntax.eff_decl)
  =
  fun env ->
    fun ed ->
      fun quals ->
        fun attrs ->
          let uu____11092 =
            let uu____11113 =
              FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
            if uu____11113
            then tc_layered_eff_decl
            else tc_non_layered_eff_decl in
          uu____11092 env ed quals attrs
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
        let fail uu____11168 =
          let uu____11169 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____11175 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____11169 uu____11175 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____11219)::(wp, uu____11221)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____11250 -> fail ())
        | uu____11251 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____11264 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____11264
       then
         let uu____11269 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____11269
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____11286 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____11286.FStar_Syntax_Syntax.pos in
       let uu____11295 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____11295 with
       | (us, lift, lift_ty) ->
           ((let uu____11309 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____11309
             then
               let uu____11314 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____11320 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____11314 uu____11320
             else ());
            (let uu____11329 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____11329 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____11347 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____11349 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____11351 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____11347 uu____11349 s uu____11351 in
                   let uu____11354 =
                     let uu____11361 =
                       let uu____11366 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____11366
                         (fun uu____11383 ->
                            match uu____11383 with
                            | (t, u) ->
                                let uu____11394 =
                                  let uu____11395 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____11395
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____11394, u)) in
                     match uu____11361 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____11414 =
                             let uu____11415 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____11415.FStar_Syntax_Syntax.n in
                           match uu____11414 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____11427)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____11455 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____11455 with
                                | (a', uu____11465)::bs1 ->
                                    let uu____11485 =
                                      let uu____11486 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____11486
                                        FStar_Pervasives_Native.fst in
                                    let uu____11552 =
                                      let uu____11565 =
                                        let uu____11568 =
                                          let uu____11569 =
                                            let uu____11576 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11576) in
                                          FStar_Syntax_Syntax.NT uu____11569 in
                                        [uu____11568] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11565 in
                                    FStar_All.pipe_right uu____11485
                                      uu____11552)
                           | uu____11591 ->
                               let uu____11592 =
                                 let uu____11598 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11598) in
                               FStar_Errors.raise_error uu____11592 r in
                         let uu____11610 =
                           let uu____11621 =
                             let uu____11626 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11633 =
                               let uu____11634 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11634
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11626 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11633 in
                           match uu____11621 with
                           | (f_sort, g) ->
                               let uu____11655 =
                                 let uu____11662 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11662
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11655, g) in
                         (match uu____11610 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11729 =
                                let uu____11734 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11735 =
                                  let uu____11736 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11736
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11734 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11735 in
                              (match uu____11729 with
                               | (repr, g_repr) ->
                                   let uu____11753 =
                                     let uu____11758 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11759 =
                                       let uu____11761 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11763 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11761 uu____11763 in
                                     pure_wp_uvar uu____11758 repr
                                       uu____11759 r in
                                   (match uu____11753 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11775 =
                                            let uu____11776 =
                                              let uu____11777 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11777] in
                                            let uu____11778 =
                                              let uu____11789 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11789] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11776;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11778;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11775 in
                                        let uu____11822 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11825 =
                                          let uu____11826 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11826 guard_wp in
                                        (uu____11822, uu____11825)))) in
                   match uu____11354 with
                   | (k, g_k) ->
                       ((let uu____11836 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11836
                         then
                           let uu____11841 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11841
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11850 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11850
                          then
                            let uu____11855 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11855
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          let check_non_informative_binders =
                            (FStar_TypeChecker_Env.is_reifiable_effect env
                               sub.FStar_Syntax_Syntax.target)
                              &&
                              (let uu____11864 =
                                 FStar_TypeChecker_Env.fv_with_lid_has_attr
                                   env sub.FStar_Syntax_Syntax.target
                                   FStar_Parser_Const.allow_informative_binders_attr in
                               Prims.op_Negation uu____11864) in
                          (let uu____11867 =
                             let uu____11868 = FStar_Syntax_Subst.compress k1 in
                             uu____11868.FStar_Syntax_Syntax.n in
                           match uu____11867 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11893 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11893 with
                                | (a::bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11924 =
                                      let uu____11943 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11943
                                        (fun uu____12019 ->
                                           match uu____12019 with
                                           | (l1, l2) ->
                                               let uu____12092 =
                                                 FStar_List.hd l2 in
                                               (l1, uu____12092)) in
                                    (match uu____11924 with
                                     | (bs2, f_b) ->
                                         let env1 =
                                           FStar_TypeChecker_Env.push_binders
                                             env [a] in
                                         validate_layered_effect_binders env1
                                           bs2
                                           [(FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort;
                                           res_t]
                                           check_non_informative_binders r)));
                          (let sub1 =
                             let uu___1222_12165 = sub in
                             let uu____12166 =
                               let uu____12169 =
                                 let uu____12170 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____12170) in
                               FStar_Pervasives_Native.Some uu____12169 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1222_12165.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1222_12165.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____12166;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____12184 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____12184
                            then
                              let uu____12189 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____12189
                            else ());
                           sub1)))))))))
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env ->
    fun sub ->
      fun r ->
        let check_and_gen1 env1 t k =
          let uu____12226 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____12226 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____12229 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____12229
        then tc_layered_lift env sub
        else
          (let uu____12236 =
             let uu____12243 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____12243 in
           match uu____12236 with
           | (a, wp_a_src) ->
               let uu____12250 =
                 let uu____12257 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____12257 in
               (match uu____12250 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____12265 =
                        let uu____12268 =
                          let uu____12269 =
                            let uu____12276 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____12276) in
                          FStar_Syntax_Syntax.NT uu____12269 in
                        [uu____12268] in
                      FStar_Syntax_Subst.subst uu____12265 wp_b_tgt in
                    let expected_k =
                      let uu____12284 =
                        let uu____12293 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____12300 =
                          let uu____12309 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____12309] in
                        uu____12293 :: uu____12300 in
                      let uu____12334 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____12284 uu____12334 in
                    let repr_type eff_name a1 wp =
                      (let uu____12356 =
                         let uu____12358 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____12358 in
                       if uu____12356
                       then
                         let uu____12361 =
                           let uu____12367 =
                             let uu____12369 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____12369 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____12367) in
                         let uu____12373 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____12361 uu____12373
                       else ());
                      (let uu____12376 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____12376 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____12409 =
                               let uu____12410 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____12410
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____12409 in
                           let uu____12417 =
                             let uu____12418 =
                               let uu____12435 =
                                 let uu____12446 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____12455 =
                                   let uu____12466 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____12466] in
                                 uu____12446 :: uu____12455 in
                               (repr, uu____12435) in
                             FStar_Syntax_Syntax.Tm_app uu____12418 in
                           let uu____12511 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____12417 uu____12511) in
                    let uu____12512 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12685 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12696 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12696 with
                              | (usubst, uvs1) ->
                                  let uu____12719 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12720 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12719, uu____12720)
                            else (env, lift_wp) in
                          (match uu____12685 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12770 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12770)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12841 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12856 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12856 with
                              | (usubst, uvs) ->
                                  let uu____12881 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12881)
                            else ([], lift) in
                          (match uu____12841 with
                           | (uvs, lift1) ->
                               ((let uu____12917 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12917
                                 then
                                   let uu____12921 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12921
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12927 =
                                   let uu____12934 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12934 lift1 in
                                 match uu____12927 with
                                 | (lift2, comp, uu____12959) ->
                                     let uu____12960 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12960 with
                                      | (uu____12989, lift_wp, lift_elab) ->
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
                                            let uu____13021 =
                                              let uu____13032 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____13032 in
                                            let uu____13049 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____13021, uu____13049)
                                          else
                                            (let uu____13078 =
                                               let uu____13089 =
                                                 let uu____13098 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____13098) in
                                               FStar_Pervasives_Native.Some
                                                 uu____13089 in
                                             let uu____13113 =
                                               let uu____13122 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____13122) in
                                             (uu____13078, uu____13113)))))) in
                    (match uu____12512 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1306_13186 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1306_13186.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1306_13186.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1306_13186.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1306_13186.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1306_13186.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1306_13186.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1306_13186.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1306_13186.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1306_13186.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1306_13186.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1306_13186.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1306_13186.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1306_13186.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1306_13186.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1306_13186.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1306_13186.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1306_13186.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1306_13186.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1306_13186.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1306_13186.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1306_13186.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1306_13186.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1306_13186.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1306_13186.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1306_13186.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1306_13186.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1306_13186.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1306_13186.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1306_13186.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1306_13186.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1306_13186.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1306_13186.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1306_13186.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1306_13186.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1306_13186.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1306_13186.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1306_13186.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1306_13186.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1306_13186.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1306_13186.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1306_13186.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1306_13186.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1306_13186.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1306_13186.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1306_13186.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1306_13186.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____13219 =
                                 let uu____13224 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____13224 with
                                 | (usubst, uvs1) ->
                                     let uu____13247 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____13248 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____13247, uu____13248) in
                               (match uu____13219 with
                                | (env2, lift2) ->
                                    let uu____13253 =
                                      let uu____13260 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____13260 in
                                    (match uu____13253 with
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
                                             let uu____13286 =
                                               let uu____13287 =
                                                 let uu____13304 =
                                                   let uu____13315 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____13324 =
                                                     let uu____13335 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____13335] in
                                                   uu____13315 :: uu____13324 in
                                                 (lift_wp1, uu____13304) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____13287 in
                                             let uu____13380 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____13286 uu____13380 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____13384 =
                                             let uu____13393 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____13400 =
                                               let uu____13409 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____13416 =
                                                 let uu____13425 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____13425] in
                                               uu____13409 :: uu____13416 in
                                             uu____13393 :: uu____13400 in
                                           let uu____13456 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____13384 uu____13456 in
                                         let uu____13459 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____13459 with
                                          | (expected_k2, uu____13469,
                                             uu____13470) ->
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
                                                   let uu____13478 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____13478)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____13486 =
                             let uu____13488 =
                               let uu____13490 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____13490
                                 FStar_List.length in
                             uu____13488 <> Prims.int_one in
                           if uu____13486
                           then
                             let uu____13513 =
                               let uu____13519 =
                                 let uu____13521 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____13523 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____13525 =
                                   let uu____13527 =
                                     let uu____13529 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____13529
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____13527
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____13521 uu____13523 uu____13525 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____13519) in
                             FStar_Errors.raise_error uu____13513 r
                           else ());
                          (let uu____13556 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____13559 =
                                  let uu____13561 =
                                    let uu____13564 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____13564
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____13561
                                    FStar_List.length in
                                uu____13559 <> Prims.int_one) in
                           if uu____13556
                           then
                             let uu____13603 =
                               let uu____13609 =
                                 let uu____13611 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____13613 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____13615 =
                                   let uu____13617 =
                                     let uu____13619 =
                                       let uu____13622 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____13622
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____13619
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____13617
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____13611 uu____13613 uu____13615 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____13609) in
                             FStar_Errors.raise_error uu____13603 r
                           else ());
                          (let uu___1343_13664 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1343_13664.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1343_13664.FStar_Syntax_Syntax.target);
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
    fun uu____13695 ->
      fun r ->
        match uu____13695 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13718 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13746 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13746 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13777 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13777 c in
                     let uu____13786 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13786, uvs1, tps1, c1)) in
            (match uu____13718 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13806 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13806 with
                  | (tps2, c2) ->
                      let uu____13821 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13821 with
                       | (tps3, env3, us) ->
                           let uu____13839 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13839 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13865)::uu____13866 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13885 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13893 =
                                    let uu____13895 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13895 in
                                  if uu____13893
                                  then
                                    let uu____13898 =
                                      let uu____13904 =
                                        let uu____13906 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13908 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13906 uu____13908 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13904) in
                                    FStar_Errors.raise_error uu____13898 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13916 =
                                    let uu____13917 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____13917 in
                                  match uu____13916 with
                                  | (uvs2, t) ->
                                      let uu____13946 =
                                        let uu____13951 =
                                          let uu____13964 =
                                            let uu____13965 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13965.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13964) in
                                        match uu____13951 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13980, c5)) -> ([], c5)
                                        | (uu____14022,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____14061 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13946 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____14093 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____14093 with
                                               | (uu____14098, t1) ->
                                                   let uu____14100 =
                                                     let uu____14106 =
                                                       let uu____14108 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____14110 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____14114 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____14108
                                                         uu____14110
                                                         uu____14114 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____14106) in
                                                   FStar_Errors.raise_error
                                                     uu____14100 r)
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
              let uu____14156 =
                let uu____14158 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14158 FStar_Ident.string_of_id in
              let uu____14160 =
                let uu____14162 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14162 FStar_Ident.string_of_id in
              let uu____14164 =
                let uu____14166 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14166 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____14156 uu____14160
                uu____14164 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____14174 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____14174 with
            | (us, t, ty) ->
                let uu____14190 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____14190 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____14203 =
                         let uu____14208 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____14208
                           (fun uu____14225 ->
                              match uu____14225 with
                              | (t1, u) ->
                                  let uu____14236 =
                                    let uu____14237 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____14237
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____14236, u)) in
                       match uu____14203 with
                       | (a, u_a) ->
                           let uu____14245 =
                             let uu____14250 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____14250
                               (fun uu____14267 ->
                                  match uu____14267 with
                                  | (t1, u) ->
                                      let uu____14278 =
                                        let uu____14279 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____14279
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____14278, u)) in
                           (match uu____14245 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____14296 =
                                    let uu____14297 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____14297.FStar_Syntax_Syntax.n in
                                  match uu____14296 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____14309) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____14337 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____14337 with
                                       | (a', uu____14347)::(b', uu____14349)::bs1
                                           ->
                                           let uu____14379 =
                                             let uu____14380 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____14380
                                               FStar_Pervasives_Native.fst in
                                           let uu____14446 =
                                             let uu____14459 =
                                               let uu____14462 =
                                                 let uu____14463 =
                                                   let uu____14470 =
                                                     let uu____14473 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____14473
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____14470) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____14463 in
                                               let uu____14486 =
                                                 let uu____14489 =
                                                   let uu____14490 =
                                                     let uu____14497 =
                                                       let uu____14500 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____14500
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____14497) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____14490 in
                                                 [uu____14489] in
                                               uu____14462 :: uu____14486 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____14459 in
                                           FStar_All.pipe_right uu____14379
                                             uu____14446)
                                  | uu____14521 ->
                                      let uu____14522 =
                                        let uu____14528 =
                                          let uu____14530 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____14532 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____14530 uu____14532 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____14528) in
                                      FStar_Errors.raise_error uu____14522 r in
                                let bs = a :: b :: rest_bs in
                                let uu____14565 =
                                  let uu____14576 =
                                    let uu____14581 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____14582 =
                                      let uu____14583 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____14583
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____14581 r m u_a uu____14582 in
                                  match uu____14576 with
                                  | (repr, g) ->
                                      let uu____14604 =
                                        let uu____14611 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____14611
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____14604, g) in
                                (match uu____14565 with
                                 | (f, guard_f) ->
                                     let uu____14643 =
                                       let x_a =
                                         let uu____14661 =
                                           let uu____14662 =
                                             let uu____14663 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____14663
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____14662 in
                                         FStar_All.pipe_right uu____14661
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____14679 =
                                         let uu____14684 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____14703 =
                                           let uu____14704 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____14704
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____14684 r n u_b uu____14703 in
                                       match uu____14679 with
                                       | (repr, g) ->
                                           let uu____14725 =
                                             let uu____14732 =
                                               let uu____14733 =
                                                 let uu____14734 =
                                                   let uu____14737 =
                                                     let uu____14740 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14740 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14737 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14734 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14733 in
                                             FStar_All.pipe_right uu____14732
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____14725, g) in
                                     (match uu____14643 with
                                      | (g, guard_g) ->
                                          let uu____14784 =
                                            let uu____14789 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14790 =
                                              let uu____14791 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14791
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14789 r p u_b uu____14790 in
                                          (match uu____14784 with
                                           | (repr, guard_repr) ->
                                               let uu____14806 =
                                                 let uu____14811 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14812 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14811
                                                   repr uu____14812 r in
                                               (match uu____14806 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14824 =
                                                        let uu____14827 =
                                                          let uu____14828 =
                                                            let uu____14829 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14829] in
                                                          let uu____14830 =
                                                            let uu____14841 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14841] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14828;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14830;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14827 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14824 in
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
                                                     (let uu____14901 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14901
                                                      then
                                                        let uu____14905 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14911 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14905
                                                          uu____14911
                                                      else ());
                                                     (let k1 =
                                                        FStar_All.pipe_right
                                                          k
                                                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                             env1) in
                                                      let check_non_informative_binders
                                                        =
                                                        (FStar_TypeChecker_Env.is_reifiable_effect
                                                           env1 p)
                                                          &&
                                                          (let uu____14924 =
                                                             FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                               env1 p
                                                               FStar_Parser_Const.allow_informative_binders_attr in
                                                           Prims.op_Negation
                                                             uu____14924) in
                                                      (let uu____14927 =
                                                         let uu____14928 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14928.FStar_Syntax_Syntax.n in
                                                       match uu____14927 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14953 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14953
                                                            with
                                                            | (a1::b1::bs2,
                                                               c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14997
                                                                  =
                                                                  let uu____15024
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____15024
                                                                    (
                                                                    fun
                                                                    uu____15109
                                                                    ->
                                                                    match uu____15109
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____15190
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____15217
                                                                    =
                                                                    let uu____15224
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____15224
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____15190,
                                                                    uu____15217)) in
                                                                (match uu____14997
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____15339
                                                                    =
                                                                    let uu____15340
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____15340.FStar_Syntax_Syntax.n in
                                                                    match uu____15339
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____15345,
                                                                    c2) ->
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    let env2
                                                                    =
                                                                    FStar_TypeChecker_Env.push_binders
                                                                    env1
                                                                    [a1; b1] in
                                                                    validate_layered_effect_binders
                                                                    env2 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    g_sort;
                                                                    res_t]
                                                                    check_non_informative_binders
                                                                    r)));
                                                      (let uu____15389 =
                                                         let uu____15395 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____15395) in
                                                       FStar_Errors.log_issue
                                                         r uu____15389);
                                                      (let uu____15399 =
                                                         let uu____15400 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____15400) in
                                                       ((us1, t),
                                                         uu____15399))))))))))))
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
            let uu____15449 =
              let uu____15451 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____15451 FStar_Ident.string_of_id in
            let uu____15453 =
              let uu____15455 =
                let uu____15457 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____15457 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____15455 in
            Prims.op_Hat uu____15449 uu____15453 in
          let uu____15460 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____15460 with
          | (us, t, ty) ->
              let uu____15476 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____15476 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____15489 =
                       let uu____15494 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____15494
                         (fun uu____15511 ->
                            match uu____15511 with
                            | (t1, u) ->
                                let uu____15522 =
                                  let uu____15523 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____15523
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____15522, u)) in
                     match uu____15489 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____15540 =
                             let uu____15541 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____15541.FStar_Syntax_Syntax.n in
                           match uu____15540 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____15553)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____15581 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____15581 with
                                | (a', uu____15591)::bs1 ->
                                    let uu____15611 =
                                      let uu____15612 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____15612
                                        FStar_Pervasives_Native.fst in
                                    let uu____15710 =
                                      let uu____15723 =
                                        let uu____15726 =
                                          let uu____15727 =
                                            let uu____15734 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____15734) in
                                          FStar_Syntax_Syntax.NT uu____15727 in
                                        [uu____15726] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____15723 in
                                    FStar_All.pipe_right uu____15611
                                      uu____15710)
                           | uu____15749 ->
                               let uu____15750 =
                                 let uu____15756 =
                                   let uu____15758 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____15760 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____15758 uu____15760 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____15756) in
                               FStar_Errors.raise_error uu____15750 r in
                         let bs = a :: rest_bs in
                         let uu____15787 =
                           let uu____15798 =
                             let uu____15803 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15804 =
                               let uu____15805 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15805
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15803 r m u uu____15804 in
                           match uu____15798 with
                           | (repr, g) ->
                               let uu____15826 =
                                 let uu____15833 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15833
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15826, g) in
                         (match uu____15787 with
                          | (f, guard_f) ->
                              let uu____15865 =
                                let uu____15870 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15871 =
                                  let uu____15872 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15872
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15870 r n u uu____15871 in
                              (match uu____15865 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15887 =
                                     let uu____15892 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15893 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15892 ret_t
                                       uu____15893 r in
                                   (match uu____15887 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15903 =
                                            let uu____15904 =
                                              let uu____15905 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15905] in
                                            let uu____15906 =
                                              let uu____15917 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15917] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15904;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15906;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15903 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15972 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15972
                                          then
                                            let uu____15977 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15977
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
                                             let uu____15987 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15987
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15991 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15991
                                            then
                                              let uu____15996 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15996
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu____16008 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation
                                                   uu____16008) in
                                            (let uu____16011 =
                                               let uu____16012 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____16012.FStar_Syntax_Syntax.n in
                                             match uu____16011 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu____16037 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu____16037 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu____16068 =
                                                        let uu____16087 =
                                                          FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_All.pipe_right
                                                          uu____16087
                                                          (fun uu____16163 ->
                                                             match uu____16163
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu____16236
                                                                   =
                                                                   FStar_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu____16236)) in
                                                      (match uu____16068 with
                                                       | (bs3, f_b) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.push_binders
                                                               env [a1] in
                                                           validate_layered_effect_binders
                                                             env1 bs3
                                                             [(FStar_Pervasives_Native.fst
                                                                 f_b).FStar_Syntax_Syntax.sort;
                                                             res_t]
                                                             check_non_informative_binders
                                                             r)));
                                            (let uu____16309 =
                                               let uu____16315 =
                                                 FStar_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu____16315) in
                                             FStar_Errors.log_issue r
                                               uu____16309);
                                            (let uu____16319 =
                                               let uu____16320 =
                                                 FStar_All.pipe_right k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu____16320) in
                                             ((us1, t), uu____16319))))))))))))