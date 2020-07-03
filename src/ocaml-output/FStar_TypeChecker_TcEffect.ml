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
              let uu____351 =
                let uu____352 = FStar_Syntax_Subst.compress repr in
                uu____352.FStar_Syntax_Syntax.n in
              match uu____351 with
              | FStar_Syntax_Syntax.Tm_app (uu____365, args) -> args
              | FStar_Syntax_Syntax.Tm_arrow (uu____391::[], c) ->
                  FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_args
              | uu____433 ->
                  let uu____434 =
                    let uu____439 =
                      let uu____440 = FStar_Syntax_Print.term_to_string repr in
                      FStar_Util.format1
                        "Unexpected repr term %s when validating layered effect combinator binders"
                        uu____440 in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____439) in
                  FStar_Errors.raise_error uu____434 r in
            let rec head_names_in_term arg =
              let uu____461 =
                let uu____462 = FStar_Syntax_Subst.compress arg in
                uu____462.FStar_Syntax_Syntax.n in
              match uu____461 with
              | FStar_Syntax_Syntax.Tm_name uu____469 -> [arg]
              | FStar_Syntax_Syntax.Tm_app (head, uu____475) ->
                  let uu____500 =
                    let uu____501 = FStar_Syntax_Subst.compress head in
                    uu____501.FStar_Syntax_Syntax.n in
                  (match uu____500 with
                   | FStar_Syntax_Syntax.Tm_name uu____508 -> [head]
                   | uu____513 -> [])
              | FStar_Syntax_Syntax.Tm_abs (uu____516, body, uu____518) ->
                  head_names_in_term body
              | uu____543 -> [] in
            let head_names_in_args args =
              let uu____572 =
                FStar_All.pipe_right args
                  (FStar_List.map FStar_Pervasives_Native.fst) in
              FStar_All.pipe_right uu____572
                (FStar_List.collect head_names_in_term) in
            let repr_names_args =
              FStar_List.collect
                (fun repr ->
                   let uu____611 = FStar_All.pipe_right repr repr_args in
                   FStar_All.pipe_right uu____611 head_names_in_args)
                repr_terms in
            (let uu____641 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____641
             then
               let uu____642 =
                 FStar_List.fold_left
                   (fun s ->
                      fun t ->
                        let uu____648 =
                          let uu____649 = FStar_Syntax_Print.term_to_string t in
                          Prims.op_Hat "; " uu____649 in
                        Prims.op_Hat s uu____648) "" repr_names_args in
               let uu____650 = FStar_Syntax_Print.binders_to_string "; " bs in
               FStar_Util.print2
                 "Checking layered effect combinator binders validity, names: %s, binders: %s\n\n"
                 uu____642 uu____650
             else ());
            (let valid_binder b =
               (FStar_List.existsb
                  (fun t ->
                     let uu____673 =
                       let uu____674 =
                         let uu____675 =
                           FStar_All.pipe_right b FStar_Pervasives_Native.fst in
                         FStar_All.pipe_right uu____675
                           FStar_Syntax_Syntax.bv_to_name in
                       FStar_Syntax_Util.eq_tm uu____674 t in
                     uu____673 = FStar_Syntax_Util.Equal) repr_names_args)
                 ||
                 (match FStar_Pervasives_Native.snd b with
                  | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                      (FStar_Syntax_Syntax.Arg_qualifier_meta_attr
                      uu____687)) -> true
                  | uu____690 -> false) in
             let invalid_binders =
               FStar_List.filter
                 (fun b -> Prims.op_Negation (valid_binder b)) bs in
             if (FStar_List.length invalid_binders) <> Prims.int_zero
             then
               (let uu____723 =
                  let uu____728 =
                    let uu____729 =
                      FStar_Syntax_Print.binders_to_string "; "
                        invalid_binders in
                    FStar_Util.format1
                      "Binders %s neither appear as repr indices nor have an associated tactic"
                      uu____729 in
                  (FStar_Errors.Fatal_UnexpectedEffect, uu____728) in
                FStar_Errors.raise_error uu____723 r)
             else ();
             if check_non_informatve_binders
             then
               (let uu____731 =
                  FStar_List.fold_left
                    (fun uu____768 ->
                       fun b ->
                         match uu____768 with
                         | (env1, bs1) ->
                             let env2 =
                               FStar_TypeChecker_Env.push_binders env1 [b] in
                             let uu____831 =
                               FStar_TypeChecker_Normalize.non_info_norm env2
                                 (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                             if uu____831
                             then (env2, bs1)
                             else (env2, (b :: bs1))) (env, []) bs in
                match uu____731 with
                | (uu____883, informative_binders) ->
                    if
                      (FStar_List.length informative_binders) <>
                        Prims.int_zero
                    then
                      let uu____907 =
                        let uu____912 =
                          let uu____913 =
                            FStar_Syntax_Print.binders_to_string "; "
                              informative_binders in
                          FStar_Util.format1
                            "Binders %s are informative while the effect is reifiable"
                            uu____913 in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____912) in
                      FStar_Errors.raise_error uu____907 r
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
          (let uu____945 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
               (FStar_Options.Other "LayeredEffectsTc") in
           if uu____945
           then
             let uu____946 = FStar_Syntax_Print.eff_decl_to_string false ed in
             FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
               uu____946
           else ());
          if
            ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <>
               Prims.int_zero)
              ||
              ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
                 Prims.int_zero)
          then
            (let uu____955 =
               let uu____960 =
                 let uu____961 =
                   let uu____962 =
                     FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                   Prims.op_Hat uu____962 ")" in
                 Prims.op_Hat
                   "Binders are not supported for layered effects ("
                   uu____961 in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____960) in
             let uu____963 =
               FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
             FStar_Errors.raise_error uu____955 uu____963)
          else ();
          (let log_combinator s uu____987 =
             match uu____987 with
             | (us, t, ty) ->
                 let uu____1015 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                     (FStar_Options.Other "LayeredEffectsTc") in
                 if uu____1015
                 then
                   let uu____1016 =
                     FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                   let uu____1017 =
                     FStar_Syntax_Print.tscheme_to_string (us, t) in
                   let uu____1022 =
                     FStar_Syntax_Print.tscheme_to_string (us, ty) in
                   FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____1016
                     s uu____1017 uu____1022
                 else () in
           let fresh_a_and_u_a a =
             let uu____1042 = FStar_Syntax_Util.type_u () in
             FStar_All.pipe_right uu____1042
               (fun uu____1059 ->
                  match uu____1059 with
                  | (t, u) ->
                      let uu____1070 =
                        let uu____1071 =
                          FStar_Syntax_Syntax.gen_bv a
                            FStar_Pervasives_Native.None t in
                        FStar_All.pipe_right uu____1071
                          FStar_Syntax_Syntax.mk_binder in
                      (uu____1070, u)) in
           let fresh_x_a x a =
             let uu____1083 =
               let uu____1084 =
                 let uu____1085 =
                   FStar_All.pipe_right a FStar_Pervasives_Native.fst in
                 FStar_All.pipe_right uu____1085
                   FStar_Syntax_Syntax.bv_to_name in
               FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
                 uu____1084 in
             FStar_All.pipe_right uu____1083 FStar_Syntax_Syntax.mk_binder in
           let check_and_gen1 =
             let uu____1117 =
               FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
             check_and_gen env0 uu____1117 in
           let signature =
             let r =
               (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
             let uu____1136 =
               check_and_gen1 "signature" Prims.int_one
                 ed.FStar_Syntax_Syntax.signature in
             match uu____1136 with
             | (sig_us, sig_t, sig_ty) ->
                 let uu____1158 =
                   FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
                 (match uu____1158 with
                  | (us, t) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                      let uu____1178 = fresh_a_and_u_a "a" in
                      (match uu____1178 with
                       | (a, u) ->
                           let rest_bs =
                             let uu____1198 =
                               let uu____1199 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____1199
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               (sig_us, sig_t) u uu____1198 in
                           let bs = a :: rest_bs in
                           let k =
                             let uu____1230 =
                               FStar_Syntax_Syntax.mk_Total
                                 FStar_Syntax_Syntax.teff in
                             FStar_Syntax_Util.arrow bs uu____1230 in
                           let g_eq = FStar_TypeChecker_Rel.teq env t k in
                           (FStar_TypeChecker_Rel.force_trivial_guard env
                              g_eq;
                            (let uu____1235 =
                               let uu____1238 =
                                 FStar_All.pipe_right k
                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                      env) in
                               FStar_Syntax_Subst.close_univ_vars us
                                 uu____1238 in
                             (sig_us, uu____1235, sig_ty))))) in
           log_combinator "signature" signature;
           (let repr =
              let repr_ts =
                let uu____1264 =
                  FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
                FStar_All.pipe_right uu____1264 FStar_Util.must in
              let r =
                (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
              let uu____1292 = check_and_gen1 "repr" Prims.int_one repr_ts in
              match uu____1292 with
              | (repr_us, repr_t, repr_ty) ->
                  let uu____1314 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                  (match uu____1314 with
                   | (us, ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                       let uu____1334 = fresh_a_and_u_a "a" in
                       (match uu____1334 with
                        | (a, u) ->
                            let rest_bs =
                              let signature_ts =
                                let uu____1355 = signature in
                                match uu____1355 with
                                | (us1, t, uu____1370) -> (us1, t) in
                              let uu____1387 =
                                let uu____1388 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst in
                                FStar_All.pipe_right uu____1388
                                  FStar_Syntax_Syntax.bv_to_name in
                              FStar_TypeChecker_Util.layered_effect_indices_as_binders
                                env r ed.FStar_Syntax_Syntax.mname
                                signature_ts u uu____1387 in
                            let bs = a :: rest_bs in
                            let k =
                              let uu____1415 =
                                let uu____1418 = FStar_Syntax_Util.type_u () in
                                FStar_All.pipe_right uu____1418
                                  (fun uu____1431 ->
                                     match uu____1431 with
                                     | (t, u1) ->
                                         let uu____1438 =
                                           let uu____1441 =
                                             FStar_TypeChecker_Env.new_u_univ
                                               () in
                                           FStar_Pervasives_Native.Some
                                             uu____1441 in
                                         FStar_Syntax_Syntax.mk_Total' t
                                           uu____1438) in
                              FStar_Syntax_Util.arrow bs uu____1415 in
                            let g = FStar_TypeChecker_Rel.teq env ty k in
                            (FStar_TypeChecker_Rel.force_trivial_guard env g;
                             (let uu____1444 =
                                let uu____1447 =
                                  FStar_All.pipe_right k
                                    (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                       env) in
                                FStar_Syntax_Subst.close_univ_vars us
                                  uu____1447 in
                              (repr_us, repr_t, uu____1444))))) in
            log_combinator "repr" repr;
            (let fresh_repr r env u a_tm =
               let signature_ts =
                 let uu____1481 = signature in
                 match uu____1481 with | (us, t, uu____1496) -> (us, t) in
               let repr_ts =
                 let uu____1514 = repr in
                 match uu____1514 with | (us, t, uu____1529) -> (us, t) in
               FStar_TypeChecker_Util.fresh_effect_repr env r
                 ed.FStar_Syntax_Syntax.mname signature_ts
                 (FStar_Pervasives_Native.Some repr_ts) u a_tm in
             let not_an_arrow_error comb n t r =
               let uu____1575 =
                 let uu____1580 =
                   let uu____1581 =
                     FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                   let uu____1582 = FStar_Util.string_of_int n in
                   let uu____1583 = FStar_Syntax_Print.tag_of_term t in
                   let uu____1584 = FStar_Syntax_Print.term_to_string t in
                   FStar_Util.format5
                     "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                     uu____1581 comb uu____1582 uu____1583 uu____1584 in
                 (FStar_Errors.Fatal_UnexpectedEffect, uu____1580) in
               FStar_Errors.raise_error uu____1575 r in
             let check_non_informative_binders =
               (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals) &&
                 (let uu____1595 =
                    FStar_Syntax_Util.has_attribute attrs
                      FStar_Parser_Const.allow_informative_binders_attr in
                  Prims.op_Negation uu____1595) in
             let return_repr =
               let return_repr_ts =
                 let uu____1614 =
                   FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
                 FStar_All.pipe_right uu____1614 FStar_Util.must in
               let r =
                 (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
               let uu____1626 =
                 check_and_gen1 "return_repr" Prims.int_one return_repr_ts in
               match uu____1626 with
               | (ret_us, ret_t, ret_ty) ->
                   let uu____1648 =
                     FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                   (match uu____1648 with
                    | (us, ty) ->
                        let env =
                          FStar_TypeChecker_Env.push_univ_vars env0 us in
                        (check_no_subtyping_for_layered_combinator env ty
                           FStar_Pervasives_Native.None;
                         (let uu____1669 = fresh_a_and_u_a "a" in
                          match uu____1669 with
                          | (a, u_a) ->
                              let x_a = fresh_x_a "x" a in
                              let rest_bs =
                                let uu____1698 =
                                  let uu____1699 =
                                    FStar_Syntax_Subst.compress ty in
                                  uu____1699.FStar_Syntax_Syntax.n in
                                match uu____1698 with
                                | FStar_Syntax_Syntax.Tm_arrow
                                    (bs, uu____1711) when
                                    (FStar_List.length bs) >=
                                      (Prims.of_int (2))
                                    ->
                                    let uu____1738 =
                                      FStar_Syntax_Subst.open_binders bs in
                                    (match uu____1738 with
                                     | (a', uu____1748)::(x', uu____1750)::bs1
                                         ->
                                         let uu____1780 =
                                           let uu____1781 =
                                             let uu____1786 =
                                               let uu____1789 =
                                                 let uu____1790 =
                                                   let uu____1797 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          a) in
                                                   (a', uu____1797) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1790 in
                                               [uu____1789] in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1786 in
                                           FStar_All.pipe_right bs1
                                             uu____1781 in
                                         let uu____1804 =
                                           let uu____1817 =
                                             let uu____1820 =
                                               let uu____1821 =
                                                 let uu____1828 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        x_a) in
                                                 (x', uu____1828) in
                                               FStar_Syntax_Syntax.NT
                                                 uu____1821 in
                                             [uu____1820] in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____1817 in
                                         FStar_All.pipe_right uu____1780
                                           uu____1804)
                                | uu____1843 ->
                                    not_an_arrow_error "return"
                                      (Prims.of_int (2)) ty r in
                              let bs = a :: x_a :: rest_bs in
                              let uu____1865 =
                                let uu____1870 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____1871 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.fst a)
                                    FStar_Syntax_Syntax.bv_to_name in
                                fresh_repr r uu____1870 u_a uu____1871 in
                              (match uu____1865 with
                               | (repr1, g) ->
                                   let k =
                                     let uu____1891 =
                                       FStar_Syntax_Syntax.mk_Total' repr1
                                         (FStar_Pervasives_Native.Some u_a) in
                                     FStar_Syntax_Util.arrow bs uu____1891 in
                                   let g_eq =
                                     FStar_TypeChecker_Rel.teq env ty k in
                                   ((let uu____1896 =
                                       FStar_TypeChecker_Env.conj_guard g
                                         g_eq in
                                     FStar_TypeChecker_Rel.force_trivial_guard
                                       env uu____1896);
                                    (let k1 =
                                       FStar_All.pipe_right k
                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                            env) in
                                     (let uu____1899 =
                                        let uu____1900 =
                                          FStar_Syntax_Subst.compress k1 in
                                        uu____1900.FStar_Syntax_Syntax.n in
                                      match uu____1899 with
                                      | FStar_Syntax_Syntax.Tm_arrow 
                                          (bs1, c) ->
                                          let uu____1925 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              c in
                                          (match uu____1925 with
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
                                     (let uu____1988 =
                                        FStar_All.pipe_right k1
                                          (FStar_Syntax_Subst.close_univ_vars
                                             us) in
                                      (ret_us, ret_t, uu____1988)))))))) in
             log_combinator "return_repr" return_repr;
             (let bind_repr =
                let bind_repr_ts =
                  let uu____2018 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                  FStar_All.pipe_right uu____2018 FStar_Util.must in
                let r =
                  (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
                let uu____2046 =
                  check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
                match uu____2046 with
                | (bind_us, bind_t, bind_ty) ->
                    let uu____2068 =
                      FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                    (match uu____2068 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2089 = fresh_a_and_u_a "a" in
                           match uu____2089 with
                           | (a, u_a) ->
                               let uu____2108 = fresh_a_and_u_a "b" in
                               (match uu____2108 with
                                | (b, u_b) ->
                                    let rest_bs =
                                      let uu____2136 =
                                        let uu____2137 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____2137.FStar_Syntax_Syntax.n in
                                      match uu____2136 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____2149) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____2176 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____2176 with
                                           | (a', uu____2186)::(b',
                                                                uu____2188)::bs1
                                               ->
                                               let uu____2218 =
                                                 let uu____2219 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (2)))) in
                                                 FStar_All.pipe_right
                                                   uu____2219
                                                   FStar_Pervasives_Native.fst in
                                               let uu____2284 =
                                                 let uu____2297 =
                                                   let uu____2300 =
                                                     let uu____2301 =
                                                       let uu____2308 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a) in
                                                       (a', uu____2308) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2301 in
                                                   let uu____2315 =
                                                     let uu____2318 =
                                                       let uu____2319 =
                                                         let uu____2326 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                b) in
                                                         (b', uu____2326) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____2319 in
                                                     [uu____2318] in
                                                   uu____2300 :: uu____2315 in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2297 in
                                               FStar_All.pipe_right
                                                 uu____2218 uu____2284)
                                      | uu____2341 ->
                                          not_an_arrow_error "bind"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: b :: rest_bs in
                                    let uu____2363 =
                                      let uu____2374 =
                                        let uu____2379 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____2380 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____2379 u_a
                                          uu____2380 in
                                      match uu____2374 with
                                      | (repr1, g) ->
                                          let uu____2395 =
                                            let uu____2402 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____2402
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____2395, g) in
                                    (match uu____2363 with
                                     | (f, guard_f) ->
                                         let uu____2441 =
                                           let x_a = fresh_x_a "x" a in
                                           let uu____2453 =
                                             let uu____2458 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env
                                                 (FStar_List.append bs [x_a]) in
                                             let uu____2477 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    b)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____2458 u_b
                                               uu____2477 in
                                           match uu____2453 with
                                           | (repr1, g) ->
                                               let uu____2492 =
                                                 let uu____2499 =
                                                   let uu____2500 =
                                                     let uu____2501 =
                                                       let uu____2504 =
                                                         let uu____2507 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             () in
                                                         FStar_Pervasives_Native.Some
                                                           uu____2507 in
                                                       FStar_Syntax_Syntax.mk_Total'
                                                         repr1 uu____2504 in
                                                     FStar_Syntax_Util.arrow
                                                       [x_a] uu____2501 in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     uu____2500 in
                                                 FStar_All.pipe_right
                                                   uu____2499
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____2492, g) in
                                         (match uu____2441 with
                                          | (g, guard_g) ->
                                              let uu____2558 =
                                                let uu____2563 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs in
                                                let uu____2564 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____2563 u_b
                                                  uu____2564 in
                                              (match uu____2558 with
                                               | (repr1, guard_repr) ->
                                                   let uu____2581 =
                                                     let uu____2586 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env bs in
                                                     let uu____2587 =
                                                       let uu____2588 =
                                                         FStar_Ident.string_of_lid
                                                           ed.FStar_Syntax_Syntax.mname in
                                                       FStar_Util.format1
                                                         "implicit for pure_wp in checking bind for %s"
                                                         uu____2588 in
                                                     pure_wp_uvar uu____2586
                                                       repr1 uu____2587 r in
                                                   (match uu____2581 with
                                                    | (pure_wp_uvar1,
                                                       g_pure_wp_uvar) ->
                                                        let k =
                                                          let uu____2606 =
                                                            let uu____2609 =
                                                              let uu____2610
                                                                =
                                                                let uu____2611
                                                                  =
                                                                  FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                [uu____2611] in
                                                              let uu____2612
                                                                =
                                                                let uu____2623
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____2623] in
                                                              {
                                                                FStar_Syntax_Syntax.comp_univs
                                                                  =
                                                                  uu____2610;
                                                                FStar_Syntax_Syntax.effect_name
                                                                  =
                                                                  FStar_Parser_Const.effect_PURE_lid;
                                                                FStar_Syntax_Syntax.result_typ
                                                                  = repr1;
                                                                FStar_Syntax_Syntax.effect_args
                                                                  =
                                                                  uu____2612;
                                                                FStar_Syntax_Syntax.flags
                                                                  = []
                                                              } in
                                                            FStar_Syntax_Syntax.mk_Comp
                                                              uu____2609 in
                                                          FStar_Syntax_Util.arrow
                                                            (FStar_List.append
                                                               bs [f; g])
                                                            uu____2606 in
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
                                                          (let uu____2684 =
                                                             let uu____2685 =
                                                               FStar_Syntax_Subst.compress
                                                                 k1 in
                                                             uu____2685.FStar_Syntax_Syntax.n in
                                                           match uu____2684
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1, c) ->
                                                               let uu____2710
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c in
                                                               (match uu____2710
                                                                with
                                                                | (a1::b1::bs2,
                                                                   c1) ->
                                                                    let res_t
                                                                    =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                    let uu____2754
                                                                    =
                                                                    let uu____2781
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____2781
                                                                    (fun
                                                                    uu____2865
                                                                    ->
                                                                    match uu____2865
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____2946
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____2973
                                                                    =
                                                                    let uu____2980
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____2980
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____2946,
                                                                    uu____2973)) in
                                                                    (match uu____2754
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____3095
                                                                    =
                                                                    let uu____3096
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____3096.FStar_Syntax_Syntax.n in
                                                                    match uu____3095
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____3101,
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
                                                          (let uu____3144 =
                                                             FStar_All.pipe_right
                                                               k1
                                                               (FStar_Syntax_Subst.close_univ_vars
                                                                  bind_us) in
                                                           (bind_us, bind_t,
                                                             uu____3144)))))))))))) in
              log_combinator "bind_repr" bind_repr;
              (let stronger_repr =
                 let stronger_repr =
                   let ts =
                     let uu____3179 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_stronger_repr in
                     FStar_All.pipe_right uu____3179 FStar_Util.must in
                   let uu____3206 =
                     let uu____3207 =
                       let uu____3210 =
                         FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____3210
                         FStar_Syntax_Subst.compress in
                     uu____3207.FStar_Syntax_Syntax.n in
                   match uu____3206 with
                   | FStar_Syntax_Syntax.Tm_unknown ->
                       let signature_ts =
                         let uu____3222 = signature in
                         match uu____3222 with
                         | (us, t, uu____3237) -> (us, t) in
                       let uu____3254 =
                         FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                           [FStar_Syntax_Syntax.U_unknown] in
                       (match uu____3254 with
                        | (uu____3263, signature_t) ->
                            let uu____3265 =
                              let uu____3266 =
                                FStar_Syntax_Subst.compress signature_t in
                              uu____3266.FStar_Syntax_Syntax.n in
                            (match uu____3265 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3274)
                                 ->
                                 let bs1 = FStar_Syntax_Subst.open_binders bs in
                                 let repr_t =
                                   let repr_ts =
                                     let uu____3300 = repr in
                                     match uu____3300 with
                                     | (us, t, uu____3315) -> (us, t) in
                                   let uu____3332 =
                                     FStar_TypeChecker_Env.inst_tscheme_with
                                       repr_ts
                                       [FStar_Syntax_Syntax.U_unknown] in
                                   FStar_All.pipe_right uu____3332
                                     FStar_Pervasives_Native.snd in
                                 let repr_t_applied =
                                   let uu____3346 =
                                     let uu____3347 =
                                       let uu____3364 =
                                         let uu____3375 =
                                           let uu____3378 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst) in
                                           FStar_All.pipe_right uu____3378
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name) in
                                         FStar_All.pipe_right uu____3375
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.as_arg) in
                                       (repr_t, uu____3364) in
                                     FStar_Syntax_Syntax.Tm_app uu____3347 in
                                   FStar_Syntax_Syntax.mk uu____3346
                                     FStar_Range.dummyRange in
                                 let f_b =
                                   FStar_Syntax_Syntax.null_binder
                                     repr_t_applied in
                                 let uu____3428 =
                                   let uu____3429 =
                                     let uu____3432 =
                                       FStar_All.pipe_right f_b
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____3432
                                       FStar_Syntax_Syntax.bv_to_name in
                                   FStar_Syntax_Util.abs
                                     (FStar_List.append bs1 [f_b]) uu____3429
                                     FStar_Pervasives_Native.None in
                                 ([], uu____3428)
                             | uu____3461 -> failwith "Impossible!"))
                   | uu____3466 -> ts in
                 let r =
                   (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
                 let uu____3468 =
                   check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
                 match uu____3468 with
                 | (stronger_us, stronger_t, stronger_ty) ->
                     ((let uu____3491 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "LayeredEffectsTc") in
                       if uu____3491
                       then
                         let uu____3492 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_t) in
                         let uu____3497 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_ty) in
                         FStar_Util.print2
                           "stronger combinator typechecked with term: %s and type: %s\n"
                           uu____3492 uu____3497
                       else ());
                      (let uu____3503 =
                         FStar_Syntax_Subst.open_univ_vars stronger_us
                           stronger_ty in
                       match uu____3503 with
                       | (us, ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____3524 = fresh_a_and_u_a "a" in
                             match uu____3524 with
                             | (a, u) ->
                                 let rest_bs =
                                   let uu____3552 =
                                     let uu____3553 =
                                       FStar_Syntax_Subst.compress ty in
                                     uu____3553.FStar_Syntax_Syntax.n in
                                   match uu____3552 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs, uu____3565) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____3592 =
                                         FStar_Syntax_Subst.open_binders bs in
                                       (match uu____3592 with
                                        | (a', uu____3602)::bs1 ->
                                            let uu____3622 =
                                              let uu____3623 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one)) in
                                              FStar_All.pipe_right uu____3623
                                                FStar_Pervasives_Native.fst in
                                            let uu____3720 =
                                              let uu____3733 =
                                                let uu____3736 =
                                                  let uu____3737 =
                                                    let uu____3744 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           a) in
                                                    (a', uu____3744) in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3737 in
                                                [uu____3736] in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____3733 in
                                            FStar_All.pipe_right uu____3622
                                              uu____3720)
                                   | uu____3759 ->
                                       not_an_arrow_error "stronger"
                                         (Prims.of_int (2)) ty r in
                                 let bs = a :: rest_bs in
                                 let uu____3775 =
                                   let uu____3786 =
                                     let uu____3791 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____3792 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name in
                                     fresh_repr r uu____3791 u uu____3792 in
                                   match uu____3786 with
                                   | (repr1, g) ->
                                       let uu____3807 =
                                         let uu____3814 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr1 in
                                         FStar_All.pipe_right uu____3814
                                           FStar_Syntax_Syntax.mk_binder in
                                       (uu____3807, g) in
                                 (match uu____3775 with
                                  | (f, guard_f) ->
                                      let uu____3853 =
                                        let uu____3858 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____3859 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____3858 u uu____3859 in
                                      (match uu____3853 with
                                       | (ret_t, guard_ret_t) ->
                                           let uu____3876 =
                                             let uu____3881 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3882 =
                                               let uu____3883 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               FStar_Util.format1
                                                 "implicit for pure_wp in checking stronger for %s"
                                                 uu____3883 in
                                             pure_wp_uvar uu____3881 ret_t
                                               uu____3882 r in
                                           (match uu____3876 with
                                            | (pure_wp_uvar1, guard_wp) ->
                                                let c =
                                                  let uu____3899 =
                                                    let uu____3900 =
                                                      let uu____3901 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          () in
                                                      [uu____3901] in
                                                    let uu____3902 =
                                                      let uu____3913 =
                                                        FStar_All.pipe_right
                                                          pure_wp_uvar1
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____3913] in
                                                    {
                                                      FStar_Syntax_Syntax.comp_univs
                                                        = uu____3900;
                                                      FStar_Syntax_Syntax.effect_name
                                                        =
                                                        FStar_Parser_Const.effect_PURE_lid;
                                                      FStar_Syntax_Syntax.result_typ
                                                        = ret_t;
                                                      FStar_Syntax_Syntax.effect_args
                                                        = uu____3902;
                                                      FStar_Syntax_Syntax.flags
                                                        = []
                                                    } in
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    uu____3899 in
                                                let k =
                                                  FStar_Syntax_Util.arrow
                                                    (FStar_List.append bs [f])
                                                    c in
                                                ((let uu____3968 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env)
                                                      (FStar_Options.Other
                                                         "LayeredEffectsTc") in
                                                  if uu____3968
                                                  then
                                                    let uu____3969 =
                                                      FStar_Syntax_Print.term_to_string
                                                        k in
                                                    FStar_Util.print1
                                                      "Expected type of subcomp before unification: %s\n"
                                                      uu____3969
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
                                                     let uu____3974 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____3974
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   (let uu____3976 =
                                                      let uu____3977 =
                                                        FStar_Syntax_Subst.compress
                                                          k1 in
                                                      uu____3977.FStar_Syntax_Syntax.n in
                                                    match uu____3976 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs1, c1) ->
                                                        let uu____4002 =
                                                          FStar_Syntax_Subst.open_comp
                                                            bs1 c1 in
                                                        (match uu____4002
                                                         with
                                                         | (a1::bs2, c2) ->
                                                             let res_t =
                                                               FStar_Syntax_Util.comp_result
                                                                 c2 in
                                                             let uu____4033 =
                                                               let uu____4052
                                                                 =
                                                                 FStar_List.splitAt
                                                                   ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                   bs2 in
                                                               FStar_All.pipe_right
                                                                 uu____4052
                                                                 (fun
                                                                    uu____4127
                                                                    ->
                                                                    match uu____4127
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____4200
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu____4200)) in
                                                             (match uu____4033
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
                                                   (let uu____4272 =
                                                      FStar_All.pipe_right k1
                                                        (FStar_Syntax_Subst.close_univ_vars
                                                           stronger_us) in
                                                    (stronger_us, stronger_t,
                                                      uu____4272)))))))))))) in
               log_combinator "stronger_repr" stronger_repr;
               (let if_then_else =
                  let if_then_else_ts =
                    let ts =
                      let uu____4307 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____4307 FStar_Util.must in
                    let uu____4334 =
                      let uu____4335 =
                        let uu____4338 =
                          FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                        FStar_All.pipe_right uu____4338
                          FStar_Syntax_Subst.compress in
                      uu____4335.FStar_Syntax_Syntax.n in
                    match uu____4334 with
                    | FStar_Syntax_Syntax.Tm_unknown ->
                        let signature_ts =
                          let uu____4350 = signature in
                          match uu____4350 with
                          | (us, t, uu____4365) -> (us, t) in
                        let uu____4382 =
                          FStar_TypeChecker_Env.inst_tscheme_with
                            signature_ts [FStar_Syntax_Syntax.U_unknown] in
                        (match uu____4382 with
                         | (uu____4391, signature_t) ->
                             let uu____4393 =
                               let uu____4394 =
                                 FStar_Syntax_Subst.compress signature_t in
                               uu____4394.FStar_Syntax_Syntax.n in
                             (match uu____4393 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4402)
                                  ->
                                  let bs1 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  let repr_t =
                                    let repr_ts =
                                      let uu____4428 = repr in
                                      match uu____4428 with
                                      | (us, t, uu____4443) -> (us, t) in
                                    let uu____4460 =
                                      FStar_TypeChecker_Env.inst_tscheme_with
                                        repr_ts
                                        [FStar_Syntax_Syntax.U_unknown] in
                                    FStar_All.pipe_right uu____4460
                                      FStar_Pervasives_Native.snd in
                                  let repr_t_applied =
                                    let uu____4474 =
                                      let uu____4475 =
                                        let uu____4492 =
                                          let uu____4503 =
                                            let uu____4506 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.map
                                                   FStar_Pervasives_Native.fst) in
                                            FStar_All.pipe_right uu____4506
                                              (FStar_List.map
                                                 FStar_Syntax_Syntax.bv_to_name) in
                                          FStar_All.pipe_right uu____4503
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.as_arg) in
                                        (repr_t, uu____4492) in
                                      FStar_Syntax_Syntax.Tm_app uu____4475 in
                                    FStar_Syntax_Syntax.mk uu____4474
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
                                  let uu____4558 =
                                    FStar_Syntax_Util.abs
                                      (FStar_List.append bs1 [f_b; g_b; b_b])
                                      repr_t_applied
                                      FStar_Pervasives_Native.None in
                                  ([], uu____4558)
                              | uu____4589 -> failwith "Impossible!"))
                    | uu____4594 -> ts in
                  let r =
                    (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                  let uu____4596 =
                    check_and_gen1 "if_then_else" Prims.int_one
                      if_then_else_ts in
                  match uu____4596 with
                  | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                      let uu____4618 =
                        FStar_Syntax_Subst.open_univ_vars if_then_else_us
                          if_then_else_t in
                      (match uu____4618 with
                       | (us, t) ->
                           let uu____4637 =
                             FStar_Syntax_Subst.open_univ_vars
                               if_then_else_us if_then_else_ty in
                           (match uu____4637 with
                            | (uu____4654, ty) ->
                                let env =
                                  FStar_TypeChecker_Env.push_univ_vars env0
                                    us in
                                (check_no_subtyping_for_layered_combinator
                                   env t (FStar_Pervasives_Native.Some ty);
                                 (let uu____4658 = fresh_a_and_u_a "a" in
                                  match uu____4658 with
                                  | (a, u_a) ->
                                      let rest_bs =
                                        let uu____4686 =
                                          let uu____4687 =
                                            FStar_Syntax_Subst.compress ty in
                                          uu____4687.FStar_Syntax_Syntax.n in
                                        match uu____4686 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu____4699) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____4726 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            (match uu____4726 with
                                             | (a', uu____4736)::bs1 ->
                                                 let uu____4756 =
                                                   let uu____4757 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (3)))) in
                                                   FStar_All.pipe_right
                                                     uu____4757
                                                     FStar_Pervasives_Native.fst in
                                                 let uu____4822 =
                                                   let uu____4835 =
                                                     let uu____4838 =
                                                       let uu____4839 =
                                                         let uu____4846 =
                                                           let uu____4849 =
                                                             FStar_All.pipe_right
                                                               a
                                                               FStar_Pervasives_Native.fst in
                                                           FStar_All.pipe_right
                                                             uu____4849
                                                             FStar_Syntax_Syntax.bv_to_name in
                                                         (a', uu____4846) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4839 in
                                                     [uu____4838] in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____4835 in
                                                 FStar_All.pipe_right
                                                   uu____4756 uu____4822)
                                        | uu____4870 ->
                                            not_an_arrow_error "if_then_else"
                                              (Prims.of_int (4)) ty r in
                                      let bs = a :: rest_bs in
                                      let uu____4886 =
                                        let uu____4897 =
                                          let uu____4902 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs in
                                          let uu____4903 =
                                            let uu____4904 =
                                              FStar_All.pipe_right a
                                                FStar_Pervasives_Native.fst in
                                            FStar_All.pipe_right uu____4904
                                              FStar_Syntax_Syntax.bv_to_name in
                                          fresh_repr r uu____4902 u_a
                                            uu____4903 in
                                        match uu____4897 with
                                        | (repr1, g) ->
                                            let uu____4925 =
                                              let uu____4932 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1 in
                                              FStar_All.pipe_right uu____4932
                                                FStar_Syntax_Syntax.mk_binder in
                                            (uu____4925, g) in
                                      (match uu____4886 with
                                       | (f_bs, guard_f) ->
                                           let uu____4971 =
                                             let uu____4982 =
                                               let uu____4987 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs in
                                               let uu____4988 =
                                                 let uu____4989 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst in
                                                 FStar_All.pipe_right
                                                   uu____4989
                                                   FStar_Syntax_Syntax.bv_to_name in
                                               fresh_repr r uu____4987 u_a
                                                 uu____4988 in
                                             match uu____4982 with
                                             | (repr1, g) ->
                                                 let uu____5010 =
                                                   let uu____5017 =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       repr1 in
                                                   FStar_All.pipe_right
                                                     uu____5017
                                                     FStar_Syntax_Syntax.mk_binder in
                                                 (uu____5010, g) in
                                           (match uu____4971 with
                                            | (g_bs, guard_g) ->
                                                let p_b =
                                                  let uu____5063 =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "p"
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.t_bool in
                                                  FStar_All.pipe_right
                                                    uu____5063
                                                    FStar_Syntax_Syntax.mk_binder in
                                                let uu____5070 =
                                                  let uu____5075 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env
                                                      (FStar_List.append bs
                                                         [p_b]) in
                                                  let uu____5094 =
                                                    let uu____5095 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst in
                                                    FStar_All.pipe_right
                                                      uu____5095
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  fresh_repr r uu____5075 u_a
                                                    uu____5094 in
                                                (match uu____5070 with
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
                                                       (let uu____5157 =
                                                          let uu____5158 =
                                                            FStar_Syntax_Subst.compress
                                                              k1 in
                                                          uu____5158.FStar_Syntax_Syntax.n in
                                                        match uu____5157 with
                                                        | FStar_Syntax_Syntax.Tm_abs
                                                            (bs1, body,
                                                             uu____5163)
                                                            ->
                                                            let uu____5188 =
                                                              FStar_Syntax_Subst.open_term
                                                                bs1 body in
                                                            (match uu____5188
                                                             with
                                                             | (a1::bs2,
                                                                body1) ->
                                                                 let uu____5216
                                                                   =
                                                                   let uu____5243
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                   FStar_All.pipe_right
                                                                    uu____5243
                                                                    (fun
                                                                    uu____5327
                                                                    ->
                                                                    match uu____5327
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5408
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5435
                                                                    =
                                                                    let uu____5442
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5442
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____5408,
                                                                    uu____5435)) in
                                                                 (match uu____5216
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
                                                       (let uu____5573 =
                                                          FStar_All.pipe_right
                                                            k1
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               if_then_else_us) in
                                                        (if_then_else_us,
                                                          uu____5573,
                                                          if_then_else_ty))))))))))) in
                log_combinator "if_then_else" if_then_else;
                (let r =
                   let uu____5587 =
                     let uu____5590 =
                       let uu____5599 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator in
                       FStar_All.pipe_right uu____5599 FStar_Util.must in
                     FStar_All.pipe_right uu____5590
                       FStar_Pervasives_Native.snd in
                   uu____5587.FStar_Syntax_Syntax.pos in
                 let binder_aq_to_arg_aq aq =
                   match aq with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5674) -> aq
                   | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                       uu____5675) ->
                       FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit false)
                   | uu____5676 -> FStar_Pervasives_Native.None in
                 let uu____5679 = if_then_else in
                 match uu____5679 with
                 | (ite_us, ite_t, uu____5694) ->
                     let uu____5707 =
                       FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                     (match uu____5707 with
                      | (us, ite_t1) ->
                          let uu____5714 =
                            let uu____5731 =
                              let uu____5732 =
                                FStar_Syntax_Subst.compress ite_t1 in
                              uu____5732.FStar_Syntax_Syntax.n in
                            match uu____5731 with
                            | FStar_Syntax_Syntax.Tm_abs
                                (bs, uu____5752, uu____5753) ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs in
                                let uu____5779 =
                                  let uu____5792 =
                                    let uu____5797 =
                                      let uu____5800 =
                                        let uu____5809 =
                                          FStar_All.pipe_right bs1
                                            (FStar_List.splitAt
                                               ((FStar_List.length bs1) -
                                                  (Prims.of_int (3)))) in
                                        FStar_All.pipe_right uu____5809
                                          FStar_Pervasives_Native.snd in
                                      FStar_All.pipe_right uu____5800
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    FStar_All.pipe_right uu____5797
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.bv_to_name) in
                                  FStar_All.pipe_right uu____5792
                                    (fun l ->
                                       let uu____5964 = l in
                                       match uu____5964 with
                                       | f::g::p::[] -> (f, g, p)) in
                                (match uu____5779 with
                                 | (f, g, p) ->
                                     let uu____6035 =
                                       let uu____6036 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env0 us in
                                       FStar_TypeChecker_Env.push_binders
                                         uu____6036 bs1 in
                                     let uu____6037 =
                                       let uu____6038 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.map
                                              (fun uu____6063 ->
                                                 match uu____6063 with
                                                 | (b, qual) ->
                                                     let uu____6082 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     (uu____6082,
                                                       (binder_aq_to_arg_aq
                                                          qual)))) in
                                       FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                         uu____6038 r in
                                     (uu____6035, uu____6037, f, g, p))
                            | uu____6091 ->
                                failwith
                                  "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                          (match uu____5714 with
                           | (env, ite_t_applied, f_t, g_t, p_t) ->
                               let uu____6125 =
                                 let uu____6134 = stronger_repr in
                                 match uu____6134 with
                                 | (uu____6155, subcomp_t, subcomp_ty) ->
                                     let uu____6170 =
                                       FStar_Syntax_Subst.open_univ_vars us
                                         subcomp_t in
                                     (match uu____6170 with
                                      | (uu____6183, subcomp_t1) ->
                                          let uu____6185 =
                                            let uu____6196 =
                                              FStar_Syntax_Subst.open_univ_vars
                                                us subcomp_ty in
                                            match uu____6196 with
                                            | (uu____6211, subcomp_ty1) ->
                                                let uu____6213 =
                                                  let uu____6214 =
                                                    FStar_Syntax_Subst.compress
                                                      subcomp_ty1 in
                                                  uu____6214.FStar_Syntax_Syntax.n in
                                                (match uu____6213 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs, uu____6228) ->
                                                     let uu____6249 =
                                                       FStar_All.pipe_right
                                                         bs
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs)
                                                               -
                                                               Prims.int_one)) in
                                                     (match uu____6249 with
                                                      | (bs_except_last,
                                                         last_b) ->
                                                          let uu____6354 =
                                                            FStar_All.pipe_right
                                                              bs_except_last
                                                              (FStar_List.map
                                                                 FStar_Pervasives_Native.snd) in
                                                          let uu____6381 =
                                                            let uu____6384 =
                                                              FStar_All.pipe_right
                                                                last_b
                                                                FStar_List.hd in
                                                            FStar_All.pipe_right
                                                              uu____6384
                                                              FStar_Pervasives_Native.snd in
                                                          (uu____6354,
                                                            uu____6381))
                                                 | uu____6427 ->
                                                     failwith
                                                       "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                          (match uu____6185 with
                                           | (aqs_except_last, last_aq) ->
                                               let uu____6460 =
                                                 let uu____6471 =
                                                   FStar_All.pipe_right
                                                     aqs_except_last
                                                     (FStar_List.map
                                                        binder_aq_to_arg_aq) in
                                                 let uu____6488 =
                                                   FStar_All.pipe_right
                                                     last_aq
                                                     binder_aq_to_arg_aq in
                                                 (uu____6471, uu____6488) in
                                               (match uu____6460 with
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
                                                    let uu____6600 = aux f_t in
                                                    let uu____6603 = aux g_t in
                                                    (uu____6600, uu____6603)))) in
                               (match uu____6125 with
                                | (subcomp_f, subcomp_g) ->
                                    let uu____6620 =
                                      let aux t =
                                        let uu____6637 =
                                          let uu____6638 =
                                            let uu____6665 =
                                              let uu____6682 =
                                                let uu____6691 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    ite_t_applied in
                                                FStar_Util.Inr uu____6691 in
                                              (uu____6682,
                                                FStar_Pervasives_Native.None) in
                                            (t, uu____6665,
                                              FStar_Pervasives_Native.None) in
                                          FStar_Syntax_Syntax.Tm_ascribed
                                            uu____6638 in
                                        FStar_Syntax_Syntax.mk uu____6637 r in
                                      let uu____6732 = aux subcomp_f in
                                      let uu____6733 = aux subcomp_g in
                                      (uu____6732, uu____6733) in
                                    (match uu____6620 with
                                     | (tm_subcomp_ascribed_f,
                                        tm_subcomp_ascribed_g) ->
                                         ((let uu____6737 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____6737
                                           then
                                             let uu____6738 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_f in
                                             let uu____6739 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_g in
                                             FStar_Util.print2
                                               "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                               uu____6738 uu____6739
                                           else ());
                                          (let uu____6741 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env tm_subcomp_ascribed_f in
                                           match uu____6741 with
                                           | (uu____6748, uu____6749, g_f) ->
                                               let g_f1 =
                                                 let uu____6752 =
                                                   let uu____6753 =
                                                     let uu____6754 =
                                                       FStar_All.pipe_right
                                                         p_t
                                                         FStar_Syntax_Util.b2t in
                                                     FStar_All.pipe_right
                                                       uu____6754
                                                       (fun uu____6757 ->
                                                          FStar_TypeChecker_Common.NonTrivial
                                                            uu____6757) in
                                                   FStar_TypeChecker_Env.guard_of_guard_formula
                                                     uu____6753 in
                                                 FStar_TypeChecker_Env.imp_guard
                                                   uu____6752 g_f in
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env g_f1;
                                                (let uu____6759 =
                                                   FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                     env
                                                     tm_subcomp_ascribed_g in
                                                 match uu____6759 with
                                                 | (uu____6766, uu____6767,
                                                    g_g) ->
                                                     let g_g1 =
                                                       let not_p =
                                                         let uu____6771 =
                                                           let uu____6772 =
                                                             FStar_Syntax_Syntax.lid_as_fv
                                                               FStar_Parser_Const.not_lid
                                                               FStar_Syntax_Syntax.delta_constant
                                                               FStar_Pervasives_Native.None in
                                                           FStar_All.pipe_right
                                                             uu____6772
                                                             FStar_Syntax_Syntax.fv_to_tm in
                                                         let uu____6773 =
                                                           let uu____6774 =
                                                             let uu____6783 =
                                                               FStar_All.pipe_right
                                                                 p_t
                                                                 FStar_Syntax_Util.b2t in
                                                             FStar_All.pipe_right
                                                               uu____6783
                                                               FStar_Syntax_Syntax.as_arg in
                                                           [uu____6774] in
                                                         FStar_Syntax_Syntax.mk_Tm_app
                                                           uu____6771
                                                           uu____6773 r in
                                                       let uu____6810 =
                                                         FStar_TypeChecker_Env.guard_of_guard_formula
                                                           (FStar_TypeChecker_Common.NonTrivial
                                                              not_p) in
                                                       FStar_TypeChecker_Env.imp_guard
                                                         uu____6810 g_g in
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
                     (let uu____6831 =
                        let uu____6836 =
                          let uu____6837 =
                            FStar_Ident.string_of_lid
                              ed.FStar_Syntax_Syntax.mname in
                          let uu____6838 =
                            FStar_Ident.string_of_lid
                              act.FStar_Syntax_Syntax.action_name in
                          let uu____6839 =
                            FStar_Syntax_Print.binders_to_string "; "
                              act.FStar_Syntax_Syntax.action_params in
                          FStar_Util.format3
                            "Action %s:%s has non-empty action params (%s)"
                            uu____6837 uu____6838 uu____6839 in
                        (FStar_Errors.Fatal_MalformedActionDeclaration,
                          uu____6836) in
                      FStar_Errors.raise_error uu____6831 r)
                   else ();
                   (let uu____6841 =
                      let uu____6846 =
                        FStar_Syntax_Subst.univ_var_opening
                          act.FStar_Syntax_Syntax.action_univs in
                      match uu____6846 with
                      | (usubst, us) ->
                          let uu____6869 =
                            FStar_TypeChecker_Env.push_univ_vars env us in
                          let uu____6870 =
                            let uu___650_6871 = act in
                            let uu____6872 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_defn in
                            let uu____6873 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_typ in
                            {
                              FStar_Syntax_Syntax.action_name =
                                (uu___650_6871.FStar_Syntax_Syntax.action_name);
                              FStar_Syntax_Syntax.action_unqualified_name =
                                (uu___650_6871.FStar_Syntax_Syntax.action_unqualified_name);
                              FStar_Syntax_Syntax.action_univs = us;
                              FStar_Syntax_Syntax.action_params =
                                (uu___650_6871.FStar_Syntax_Syntax.action_params);
                              FStar_Syntax_Syntax.action_defn = uu____6872;
                              FStar_Syntax_Syntax.action_typ = uu____6873
                            } in
                          (uu____6869, uu____6870) in
                    match uu____6841 with
                    | (env1, act1) ->
                        let act_typ =
                          let uu____6877 =
                            let uu____6878 =
                              FStar_Syntax_Subst.compress
                                act1.FStar_Syntax_Syntax.action_typ in
                            uu____6878.FStar_Syntax_Syntax.n in
                          match uu____6877 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                              let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                              let uu____6904 =
                                FStar_Ident.lid_equals
                                  ct.FStar_Syntax_Syntax.effect_name
                                  ed.FStar_Syntax_Syntax.mname in
                              if uu____6904
                              then
                                let repr_ts =
                                  let uu____6906 = repr in
                                  match uu____6906 with
                                  | (us, t, uu____6921) -> (us, t) in
                                let repr1 =
                                  let uu____6939 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      repr_ts
                                      ct.FStar_Syntax_Syntax.comp_univs in
                                  FStar_All.pipe_right uu____6939
                                    FStar_Pervasives_Native.snd in
                                let repr2 =
                                  let uu____6949 =
                                    let uu____6950 =
                                      FStar_Syntax_Syntax.as_arg
                                        ct.FStar_Syntax_Syntax.result_typ in
                                    uu____6950 ::
                                      (ct.FStar_Syntax_Syntax.effect_args) in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____6949 r in
                                let c1 =
                                  let uu____6968 =
                                    let uu____6971 =
                                      FStar_TypeChecker_Env.new_u_univ () in
                                    FStar_Pervasives_Native.Some uu____6971 in
                                  FStar_Syntax_Syntax.mk_Total' repr2
                                    uu____6968 in
                                FStar_Syntax_Util.arrow bs c1
                              else act1.FStar_Syntax_Syntax.action_typ
                          | uu____6973 -> act1.FStar_Syntax_Syntax.action_typ in
                        let uu____6974 =
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                            act_typ in
                        (match uu____6974 with
                         | (act_typ1, uu____6982, g_t) ->
                             let uu____6984 =
                               let uu____6991 =
                                 let uu___675_6992 =
                                   FStar_TypeChecker_Env.set_expected_typ
                                     env1 act_typ1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___675_6992.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___675_6992.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___675_6992.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___675_6992.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___675_6992.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___675_6992.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___675_6992.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___675_6992.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___675_6992.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___675_6992.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     false;
                                   FStar_TypeChecker_Env.effects =
                                     (uu___675_6992.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___675_6992.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___675_6992.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___675_6992.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___675_6992.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___675_6992.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___675_6992.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___675_6992.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___675_6992.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___675_6992.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___675_6992.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___675_6992.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___675_6992.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___675_6992.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___675_6992.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___675_6992.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___675_6992.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___675_6992.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___675_6992.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___675_6992.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___675_6992.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___675_6992.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___675_6992.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___675_6992.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___675_6992.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___675_6992.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___675_6992.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___675_6992.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___675_6992.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___675_6992.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___675_6992.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___675_6992.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___675_6992.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___675_6992.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___675_6992.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___675_6992.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 } in
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 uu____6991
                                 act1.FStar_Syntax_Syntax.action_defn in
                             (match uu____6984 with
                              | (act_defn, uu____6994, g_d) ->
                                  ((let uu____6997 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other
                                           "LayeredEffectsTc") in
                                    if uu____6997
                                    then
                                      let uu____6998 =
                                        FStar_Syntax_Print.term_to_string
                                          act_defn in
                                      let uu____6999 =
                                        FStar_Syntax_Print.term_to_string
                                          act_typ1 in
                                      FStar_Util.print2
                                        "Typechecked action definition: %s and action type: %s\n"
                                        uu____6998 uu____6999
                                    else ());
                                   (let uu____7001 =
                                      let act_typ2 =
                                        FStar_TypeChecker_Normalize.normalize
                                          [FStar_TypeChecker_Env.Beta] env1
                                          act_typ1 in
                                      let uu____7009 =
                                        let uu____7010 =
                                          FStar_Syntax_Subst.compress
                                            act_typ2 in
                                        uu____7010.FStar_Syntax_Syntax.n in
                                      match uu____7009 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____7020) ->
                                          let bs1 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          let env2 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 bs1 in
                                          let uu____7043 =
                                            FStar_Syntax_Util.type_u () in
                                          (match uu____7043 with
                                           | (t, u) ->
                                               let reason =
                                                 let uu____7057 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname in
                                                 let uu____7058 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name in
                                                 FStar_Util.format2
                                                   "implicit for return type of action %s:%s"
                                                   uu____7057 uu____7058 in
                                               let uu____7059 =
                                                 FStar_TypeChecker_Util.new_implicit_var
                                                   reason r env2 t in
                                               (match uu____7059 with
                                                | (a_tm, uu____7079, g_tm) ->
                                                    let uu____7093 =
                                                      fresh_repr r env2 u
                                                        a_tm in
                                                    (match uu____7093 with
                                                     | (repr1, g) ->
                                                         let uu____7106 =
                                                           let uu____7109 =
                                                             let uu____7112 =
                                                               let uu____7115
                                                                 =
                                                                 FStar_TypeChecker_Env.new_u_univ
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 uu____7115
                                                                 (fun
                                                                    uu____7118
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7118) in
                                                             FStar_Syntax_Syntax.mk_Total'
                                                               repr1
                                                               uu____7112 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7109 in
                                                         let uu____7119 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             g g_tm in
                                                         (uu____7106,
                                                           uu____7119))))
                                      | uu____7122 ->
                                          let uu____7123 =
                                            let uu____7128 =
                                              let uu____7129 =
                                                FStar_Ident.string_of_lid
                                                  ed.FStar_Syntax_Syntax.mname in
                                              let uu____7130 =
                                                FStar_Ident.string_of_lid
                                                  act1.FStar_Syntax_Syntax.action_name in
                                              let uu____7131 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.format3
                                                "Unexpected non-function type for action %s:%s (%s)"
                                                uu____7129 uu____7130
                                                uu____7131 in
                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                              uu____7128) in
                                          FStar_Errors.raise_error uu____7123
                                            r in
                                    match uu____7001 with
                                    | (k, g_k) ->
                                        ((let uu____7145 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____7145
                                          then
                                            let uu____7146 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print1
                                              "Expected action type: %s\n"
                                              uu____7146
                                          else ());
                                         (let g =
                                            FStar_TypeChecker_Rel.teq env1
                                              act_typ1 k in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env1) [g_t; g_d; g_k; g];
                                          (let uu____7151 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____7151
                                           then
                                             let uu____7152 =
                                               FStar_Syntax_Print.term_to_string
                                                 k in
                                             FStar_Util.print1
                                               "Expected action type after unification: %s\n"
                                               uu____7152
                                           else ());
                                          (let act_typ2 =
                                             let err_msg t =
                                               let uu____7161 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____7162 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               let uu____7163 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t in
                                               FStar_Util.format3
                                                 "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                 uu____7161 uu____7162
                                                 uu____7163 in
                                             let repr_args t =
                                               let uu____7182 =
                                                 let uu____7183 =
                                                   FStar_Syntax_Subst.compress
                                                     t in
                                                 uu____7183.FStar_Syntax_Syntax.n in
                                               match uu____7182 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (head, a::is) ->
                                                   let uu____7235 =
                                                     let uu____7236 =
                                                       FStar_Syntax_Subst.compress
                                                         head in
                                                     uu____7236.FStar_Syntax_Syntax.n in
                                                   (match uu____7235 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (uu____7245, us) ->
                                                        (us,
                                                          (FStar_Pervasives_Native.fst
                                                             a), is)
                                                    | uu____7255 ->
                                                        let uu____7256 =
                                                          let uu____7261 =
                                                            err_msg t in
                                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                            uu____7261) in
                                                        FStar_Errors.raise_error
                                                          uu____7256 r)
                                               | uu____7268 ->
                                                   let uu____7269 =
                                                     let uu____7274 =
                                                       err_msg t in
                                                     (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                       uu____7274) in
                                                   FStar_Errors.raise_error
                                                     uu____7269 r in
                                             let k1 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.Beta]
                                                 env1 k in
                                             let uu____7282 =
                                               let uu____7283 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____7283.FStar_Syntax_Syntax.n in
                                             match uu____7282 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs, c) ->
                                                 let uu____7308 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c in
                                                 (match uu____7308 with
                                                  | (bs1, c1) ->
                                                      let uu____7315 =
                                                        repr_args
                                                          (FStar_Syntax_Util.comp_result
                                                             c1) in
                                                      (match uu____7315 with
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
                                                           let uu____7326 =
                                                             FStar_Syntax_Syntax.mk_Comp
                                                               ct in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7326))
                                             | uu____7329 ->
                                                 let uu____7330 =
                                                   let uu____7335 =
                                                     err_msg k1 in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____7335) in
                                                 FStar_Errors.raise_error
                                                   uu____7330 r in
                                           (let uu____7337 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env1)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____7337
                                            then
                                              let uu____7338 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.print1
                                                "Action type after injecting it into the monad: %s\n"
                                                uu____7338
                                            else ());
                                           (let act2 =
                                              let uu____7341 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env1 act_defn in
                                              match uu____7341 with
                                              | (us, act_defn1) ->
                                                  if
                                                    act1.FStar_Syntax_Syntax.action_univs
                                                      = []
                                                  then
                                                    let uu___748_7354 = act1 in
                                                    let uu____7355 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        us act_typ2 in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___748_7354.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___748_7354.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = us;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___748_7354.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = act_defn1;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu____7355
                                                    }
                                                  else
                                                    (let uu____7357 =
                                                       ((FStar_List.length us)
                                                          =
                                                          (FStar_List.length
                                                             act1.FStar_Syntax_Syntax.action_univs))
                                                         &&
                                                         (FStar_List.forall2
                                                            (fun u1 ->
                                                               fun u2 ->
                                                                 let uu____7363
                                                                   =
                                                                   FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                 uu____7363 =
                                                                   Prims.int_zero)
                                                            us
                                                            act1.FStar_Syntax_Syntax.action_univs) in
                                                     if uu____7357
                                                     then
                                                       let uu___753_7364 =
                                                         act1 in
                                                       let uu____7365 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           act1.FStar_Syntax_Syntax.action_univs
                                                           act_typ2 in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___753_7364.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___753_7364.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           =
                                                           (uu___753_7364.FStar_Syntax_Syntax.action_univs);
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___753_7364.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7365
                                                       }
                                                     else
                                                       (let uu____7367 =
                                                          let uu____7372 =
                                                            let uu____7373 =
                                                              FStar_Ident.string_of_lid
                                                                ed.FStar_Syntax_Syntax.mname in
                                                            let uu____7374 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____7375 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                us in
                                                            let uu____7376 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                act1.FStar_Syntax_Syntax.action_univs in
                                                            FStar_Util.format4
                                                              "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                              uu____7373
                                                              uu____7374
                                                              uu____7375
                                                              uu____7376 in
                                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                            uu____7372) in
                                                        FStar_Errors.raise_error
                                                          uu____7367 r)) in
                                            act2))))))))) in
                 let tschemes_of uu____7398 =
                   match uu____7398 with | (us, t, ty) -> ((us, t), (us, ty)) in
                 let combinators =
                   let uu____7443 =
                     let uu____7444 = tschemes_of repr in
                     let uu____7449 = tschemes_of return_repr in
                     let uu____7454 = tschemes_of bind_repr in
                     let uu____7459 = tschemes_of stronger_repr in
                     let uu____7464 = tschemes_of if_then_else in
                     {
                       FStar_Syntax_Syntax.l_repr = uu____7444;
                       FStar_Syntax_Syntax.l_return = uu____7449;
                       FStar_Syntax_Syntax.l_bind = uu____7454;
                       FStar_Syntax_Syntax.l_subcomp = uu____7459;
                       FStar_Syntax_Syntax.l_if_then_else = uu____7464
                     } in
                   FStar_Syntax_Syntax.Layered_eff uu____7443 in
                 let uu___762_7469 = ed in
                 let uu____7470 =
                   FStar_List.map (tc_action env0)
                     ed.FStar_Syntax_Syntax.actions in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___762_7469.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___762_7469.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs =
                     (uu___762_7469.FStar_Syntax_Syntax.univs);
                   FStar_Syntax_Syntax.binders =
                     (uu___762_7469.FStar_Syntax_Syntax.binders);
                   FStar_Syntax_Syntax.signature =
                     (let uu____7477 = signature in
                      match uu____7477 with | (us, t, uu____7492) -> (us, t));
                   FStar_Syntax_Syntax.combinators = combinators;
                   FStar_Syntax_Syntax.actions = uu____7470;
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___762_7469.FStar_Syntax_Syntax.eff_attrs)
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
          (let uu____7538 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
               (FStar_Options.Other "ED") in
           if uu____7538
           then
             let uu____7539 = FStar_Syntax_Print.eff_decl_to_string false ed in
             FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____7539
           else ());
          (let uu____7541 =
             let uu____7546 =
               FStar_Syntax_Subst.univ_var_opening
                 ed.FStar_Syntax_Syntax.univs in
             match uu____7546 with
             | (ed_univs_subst, ed_univs) ->
                 let bs =
                   let uu____7570 =
                     FStar_Syntax_Subst.subst_binders ed_univs_subst
                       ed.FStar_Syntax_Syntax.binders in
                   FStar_Syntax_Subst.open_binders uu____7570 in
                 let uu____7571 =
                   let uu____7578 =
                     FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                   FStar_TypeChecker_TcTerm.tc_tparams uu____7578 bs in
                 (match uu____7571 with
                  | (bs1, uu____7584, uu____7585) ->
                      let uu____7586 =
                        let tmp_t =
                          let uu____7596 =
                            let uu____7599 =
                              FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                                (fun uu____7604 ->
                                   FStar_Pervasives_Native.Some uu____7604) in
                            FStar_Syntax_Syntax.mk_Total'
                              FStar_Syntax_Syntax.t_unit uu____7599 in
                          FStar_Syntax_Util.arrow bs1 uu____7596 in
                        let uu____7605 =
                          FStar_TypeChecker_Util.generalize_universes env0
                            tmp_t in
                        match uu____7605 with
                        | (us, tmp_t1) ->
                            let uu____7622 =
                              let uu____7623 =
                                let uu____7624 =
                                  FStar_All.pipe_right tmp_t1
                                    FStar_Syntax_Util.arrow_formals in
                                FStar_All.pipe_right uu____7624
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____7623
                                FStar_Syntax_Subst.close_binders in
                            (us, uu____7622) in
                      (match uu____7586 with
                       | (us, bs2) ->
                           (match ed_univs with
                            | [] -> (us, bs2)
                            | uu____7661 ->
                                let uu____7664 =
                                  ((FStar_List.length ed_univs) =
                                     (FStar_List.length us))
                                    &&
                                    (FStar_List.forall2
                                       (fun u1 ->
                                          fun u2 ->
                                            let uu____7670 =
                                              FStar_Syntax_Syntax.order_univ_name
                                                u1 u2 in
                                            uu____7670 = Prims.int_zero)
                                       ed_univs us) in
                                if uu____7664
                                then (us, bs2)
                                else
                                  (let uu____7676 =
                                     let uu____7681 =
                                       let uu____7682 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____7683 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length ed_univs) in
                                       let uu____7684 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length us) in
                                       FStar_Util.format3
                                         "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                         uu____7682 uu____7683 uu____7684 in
                                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                       uu____7681) in
                                   let uu____7685 =
                                     FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname in
                                   FStar_Errors.raise_error uu____7676
                                     uu____7685)))) in
           match uu____7541 with
           | (us, bs) ->
               let ed1 =
                 let uu___797_7693 = ed in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___797_7693.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___797_7693.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs = us;
                   FStar_Syntax_Syntax.binders = bs;
                   FStar_Syntax_Syntax.signature =
                     (uu___797_7693.FStar_Syntax_Syntax.signature);
                   FStar_Syntax_Syntax.combinators =
                     (uu___797_7693.FStar_Syntax_Syntax.combinators);
                   FStar_Syntax_Syntax.actions =
                     (uu___797_7693.FStar_Syntax_Syntax.actions);
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___797_7693.FStar_Syntax_Syntax.eff_attrs)
                 } in
               let uu____7694 = FStar_Syntax_Subst.univ_var_opening us in
               (match uu____7694 with
                | (ed_univs_subst, ed_univs) ->
                    let uu____7713 =
                      let uu____7718 =
                        FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                      FStar_Syntax_Subst.open_binders' uu____7718 in
                    (match uu____7713 with
                     | (ed_bs, ed_bs_subst) ->
                         let ed2 =
                           let op uu____7739 =
                             match uu____7739 with
                             | (us1, t) ->
                                 let t1 =
                                   let uu____7759 =
                                     FStar_Syntax_Subst.shift_subst
                                       ((FStar_List.length ed_bs) +
                                          (FStar_List.length us1))
                                       ed_univs_subst in
                                   FStar_Syntax_Subst.subst uu____7759 t in
                                 let uu____7768 =
                                   let uu____7769 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length us1) ed_bs_subst in
                                   FStar_Syntax_Subst.subst uu____7769 t1 in
                                 (us1, uu____7768) in
                           let uu___811_7774 = ed1 in
                           let uu____7775 =
                             op ed1.FStar_Syntax_Syntax.signature in
                           let uu____7776 =
                             FStar_Syntax_Util.apply_eff_combinators op
                               ed1.FStar_Syntax_Syntax.combinators in
                           let uu____7777 =
                             FStar_List.map
                               (fun a ->
                                  let uu___814_7785 = a in
                                  let uu____7786 =
                                    let uu____7787 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____7787 in
                                  let uu____7798 =
                                    let uu____7799 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____7799 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      (uu___814_7785.FStar_Syntax_Syntax.action_name);
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (uu___814_7785.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (uu___814_7785.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (uu___814_7785.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____7786;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____7798
                                  }) ed1.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___811_7774.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___811_7774.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs =
                               (uu___811_7774.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders =
                               (uu___811_7774.FStar_Syntax_Syntax.binders);
                             FStar_Syntax_Syntax.signature = uu____7775;
                             FStar_Syntax_Syntax.combinators = uu____7776;
                             FStar_Syntax_Syntax.actions = uu____7777;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___811_7774.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         ((let uu____7811 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____7811
                           then
                             let uu____7812 =
                               FStar_Syntax_Print.eff_decl_to_string false
                                 ed2 in
                             FStar_Util.print1
                               "After typechecking binders eff_decl: \n\t%s\n"
                               uu____7812
                           else ());
                          (let env =
                             let uu____7815 =
                               FStar_TypeChecker_Env.push_univ_vars env0
                                 ed_univs in
                             FStar_TypeChecker_Env.push_binders uu____7815
                               ed_bs in
                           let check_and_gen' comb n env_opt uu____7848 k =
                             match uu____7848 with
                             | (us1, t) ->
                                 let env1 =
                                   if FStar_Util.is_some env_opt
                                   then
                                     FStar_All.pipe_right env_opt
                                       FStar_Util.must
                                   else env in
                                 let uu____7864 =
                                   FStar_Syntax_Subst.open_univ_vars us1 t in
                                 (match uu____7864 with
                                  | (us2, t1) ->
                                      let t2 =
                                        match k with
                                        | FStar_Pervasives_Native.Some k1 ->
                                            let uu____7873 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                              uu____7873 t1 k1
                                        | FStar_Pervasives_Native.None ->
                                            let uu____7874 =
                                              let uu____7881 =
                                                FStar_TypeChecker_Env.push_univ_vars
                                                  env1 us2 in
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                uu____7881 t1 in
                                            (match uu____7874 with
                                             | (t2, uu____7883, g) ->
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env1 g;
                                                  t2)) in
                                      let uu____7886 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env1 t2 in
                                      (match uu____7886 with
                                       | (g_us, t3) ->
                                           (if (FStar_List.length g_us) <> n
                                            then
                                              (let error =
                                                 let uu____7899 =
                                                   FStar_Ident.string_of_lid
                                                     ed2.FStar_Syntax_Syntax.mname in
                                                 let uu____7900 =
                                                   FStar_Util.string_of_int n in
                                                 let uu____7901 =
                                                   let uu____7902 =
                                                     FStar_All.pipe_right
                                                       g_us FStar_List.length in
                                                   FStar_All.pipe_right
                                                     uu____7902
                                                     FStar_Util.string_of_int in
                                                 FStar_Util.format4
                                                   "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                   uu____7899 comb uu____7900
                                                   uu____7901 in
                                               FStar_Errors.raise_error
                                                 (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                   error)
                                                 t3.FStar_Syntax_Syntax.pos)
                                            else ();
                                            (match us2 with
                                             | [] -> (g_us, t3)
                                             | uu____7910 ->
                                                 let uu____7911 =
                                                   ((FStar_List.length us2) =
                                                      (FStar_List.length g_us))
                                                     &&
                                                     (FStar_List.forall2
                                                        (fun u1 ->
                                                           fun u2 ->
                                                             let uu____7917 =
                                                               FStar_Syntax_Syntax.order_univ_name
                                                                 u1 u2 in
                                                             uu____7917 =
                                                               Prims.int_zero)
                                                        us2 g_us) in
                                                 if uu____7911
                                                 then (g_us, t3)
                                                 else
                                                   (let uu____7923 =
                                                      let uu____7928 =
                                                        let uu____7929 =
                                                          FStar_Ident.string_of_lid
                                                            ed2.FStar_Syntax_Syntax.mname in
                                                        let uu____7930 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               us2) in
                                                        let uu____7931 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               g_us) in
                                                        FStar_Util.format4
                                                          "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                          uu____7929 comb
                                                          uu____7930
                                                          uu____7931 in
                                                      (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                        uu____7928) in
                                                    FStar_Errors.raise_error
                                                      uu____7923
                                                      t3.FStar_Syntax_Syntax.pos))))) in
                           let signature =
                             check_and_gen' "signature" Prims.int_one
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature
                               FStar_Pervasives_Native.None in
                           (let uu____7934 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "ED") in
                            if uu____7934
                            then
                              let uu____7935 =
                                FStar_Syntax_Print.tscheme_to_string
                                  signature in
                              FStar_Util.print1 "Typechecked signature: %s\n"
                                uu____7935
                            else ());
                           (let fresh_a_and_wp uu____7948 =
                              let fail t =
                                let uu____7961 =
                                  FStar_TypeChecker_Err.unexpected_signature_for_monad
                                    env ed2.FStar_Syntax_Syntax.mname t in
                                FStar_Errors.raise_error uu____7961
                                  (FStar_Pervasives_Native.snd
                                     ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                              let uu____7976 =
                                FStar_TypeChecker_Env.inst_tscheme signature in
                              match uu____7976 with
                              | (uu____7987, signature1) ->
                                  let uu____7989 =
                                    let uu____7990 =
                                      FStar_Syntax_Subst.compress signature1 in
                                    uu____7990.FStar_Syntax_Syntax.n in
                                  (match uu____7989 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs1, uu____8000) ->
                                       let bs2 =
                                         FStar_Syntax_Subst.open_binders bs1 in
                                       (match bs2 with
                                        | (a, uu____8029)::(wp, uu____8031)::[]
                                            ->
                                            (a,
                                              (wp.FStar_Syntax_Syntax.sort))
                                        | uu____8060 -> fail signature1)
                                   | uu____8061 -> fail signature1) in
                            let log_combinator s ts =
                              let uu____8073 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "ED") in
                              if uu____8073
                              then
                                let uu____8074 =
                                  FStar_Ident.string_of_lid
                                    ed2.FStar_Syntax_Syntax.mname in
                                let uu____8075 =
                                  FStar_Syntax_Print.tscheme_to_string ts in
                                FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                  uu____8074 s uu____8075
                              else () in
                            let ret_wp =
                              let uu____8078 = fresh_a_and_wp () in
                              match uu____8078 with
                              | (a, wp_sort) ->
                                  let k =
                                    let uu____8094 =
                                      let uu____8103 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____8110 =
                                        let uu____8119 =
                                          let uu____8126 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____8126 in
                                        [uu____8119] in
                                      uu____8103 :: uu____8110 in
                                    let uu____8145 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                    FStar_Syntax_Util.arrow uu____8094
                                      uu____8145 in
                                  let uu____8148 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_return_vc_combinator in
                                  check_and_gen' "ret_wp" Prims.int_one
                                    FStar_Pervasives_Native.None uu____8148
                                    (FStar_Pervasives_Native.Some k) in
                            log_combinator "ret_wp" ret_wp;
                            (let bind_wp =
                               let uu____8159 = fresh_a_and_wp () in
                               match uu____8159 with
                               | (a, wp_sort_a) ->
                                   let uu____8172 = fresh_a_and_wp () in
                                   (match uu____8172 with
                                    | (b, wp_sort_b) ->
                                        let wp_sort_a_b =
                                          let uu____8188 =
                                            let uu____8197 =
                                              let uu____8204 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____8204 in
                                            [uu____8197] in
                                          let uu____8217 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8188
                                            uu____8217 in
                                        let k =
                                          let uu____8223 =
                                            let uu____8232 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_range in
                                            let uu____8239 =
                                              let uu____8248 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu____8255 =
                                                let uu____8264 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b in
                                                let uu____8271 =
                                                  let uu____8280 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu____8287 =
                                                    let uu____8296 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a_b in
                                                    [uu____8296] in
                                                  uu____8280 :: uu____8287 in
                                                uu____8264 :: uu____8271 in
                                              uu____8248 :: uu____8255 in
                                            uu____8232 :: uu____8239 in
                                          let uu____8339 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8223
                                            uu____8339 in
                                        let uu____8342 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_bind_vc_combinator in
                                        check_and_gen' "bind_wp"
                                          (Prims.of_int (2))
                                          FStar_Pervasives_Native.None
                                          uu____8342
                                          (FStar_Pervasives_Native.Some k)) in
                             log_combinator "bind_wp" bind_wp;
                             (let stronger =
                                let uu____8353 = fresh_a_and_wp () in
                                match uu____8353 with
                                | (a, wp_sort_a) ->
                                    let uu____8366 =
                                      FStar_Syntax_Util.type_u () in
                                    (match uu____8366 with
                                     | (t, uu____8372) ->
                                         let k =
                                           let uu____8376 =
                                             let uu____8385 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a in
                                             let uu____8392 =
                                               let uu____8401 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               let uu____8408 =
                                                 let uu____8417 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____8417] in
                                               uu____8401 :: uu____8408 in
                                             uu____8385 :: uu____8392 in
                                           let uu____8448 =
                                             FStar_Syntax_Syntax.mk_Total t in
                                           FStar_Syntax_Util.arrow uu____8376
                                             uu____8448 in
                                         let uu____8451 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_stronger_vc_combinator in
                                         check_and_gen' "stronger"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           uu____8451
                                           (FStar_Pervasives_Native.Some k)) in
                              log_combinator "stronger" stronger;
                              (let if_then_else =
                                 let uu____8462 = fresh_a_and_wp () in
                                 match uu____8462 with
                                 | (a, wp_sort_a) ->
                                     let p =
                                       let uu____8476 =
                                         let uu____8479 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____8479 in
                                       let uu____8480 =
                                         let uu____8481 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____8481
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____8476
                                         uu____8480 in
                                     let k =
                                       let uu____8493 =
                                         let uu____8502 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____8509 =
                                           let uu____8518 =
                                             FStar_Syntax_Syntax.mk_binder p in
                                           let uu____8525 =
                                             let uu____8534 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____8541 =
                                               let uu____8550 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____8550] in
                                             uu____8534 :: uu____8541 in
                                           uu____8518 :: uu____8525 in
                                         uu____8502 :: uu____8509 in
                                       let uu____8587 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____8493
                                         uu____8587 in
                                     let uu____8590 =
                                       let uu____8595 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                       FStar_All.pipe_right uu____8595
                                         FStar_Util.must in
                                     check_and_gen' "if_then_else"
                                       Prims.int_one
                                       FStar_Pervasives_Native.None
                                       uu____8590
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "if_then_else" if_then_else;
                               (let ite_wp =
                                  let uu____8624 = fresh_a_and_wp () in
                                  match uu____8624 with
                                  | (a, wp_sort_a) ->
                                      let k =
                                        let uu____8640 =
                                          let uu____8649 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____8656 =
                                            let uu____8665 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a in
                                            [uu____8665] in
                                          uu____8649 :: uu____8656 in
                                        let uu____8690 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_a in
                                        FStar_Syntax_Util.arrow uu____8640
                                          uu____8690 in
                                      let uu____8693 =
                                        let uu____8698 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_wp_ite_combinator in
                                        FStar_All.pipe_right uu____8698
                                          FStar_Util.must in
                                      check_and_gen' "ite_wp" Prims.int_one
                                        FStar_Pervasives_Native.None
                                        uu____8693
                                        (FStar_Pervasives_Native.Some k) in
                                log_combinator "ite_wp" ite_wp;
                                (let close_wp =
                                   let uu____8711 = fresh_a_and_wp () in
                                   match uu____8711 with
                                   | (a, wp_sort_a) ->
                                       let b =
                                         let uu____8725 =
                                           let uu____8728 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname in
                                           FStar_Pervasives_Native.Some
                                             uu____8728 in
                                         let uu____8729 =
                                           let uu____8730 =
                                             FStar_Syntax_Util.type_u () in
                                           FStar_All.pipe_right uu____8730
                                             FStar_Pervasives_Native.fst in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____8725 uu____8729 in
                                       let wp_sort_b_a =
                                         let uu____8742 =
                                           let uu____8751 =
                                             let uu____8758 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 b in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____8758 in
                                           [uu____8751] in
                                         let uu____8771 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____8742
                                           uu____8771 in
                                       let k =
                                         let uu____8777 =
                                           let uu____8786 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____8793 =
                                             let uu____8802 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____8809 =
                                               let uu____8818 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_b_a in
                                               [uu____8818] in
                                             uu____8802 :: uu____8809 in
                                           uu____8786 :: uu____8793 in
                                         let uu____8849 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____8777
                                           uu____8849 in
                                       let uu____8852 =
                                         let uu____8857 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_wp_close_combinator in
                                         FStar_All.pipe_right uu____8857
                                           FStar_Util.must in
                                       check_and_gen' "close_wp"
                                         (Prims.of_int (2))
                                         FStar_Pervasives_Native.None
                                         uu____8852
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "close_wp" close_wp;
                                 (let trivial =
                                    let uu____8870 = fresh_a_and_wp () in
                                    match uu____8870 with
                                    | (a, wp_sort_a) ->
                                        let uu____8883 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____8883 with
                                         | (t, uu____8889) ->
                                             let k =
                                               let uu____8893 =
                                                 let uu____8902 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a in
                                                 let uu____8909 =
                                                   let uu____8918 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a in
                                                   [uu____8918] in
                                                 uu____8902 :: uu____8909 in
                                               let uu____8943 =
                                                 FStar_Syntax_Syntax.mk_GTotal
                                                   t in
                                               FStar_Syntax_Util.arrow
                                                 uu____8893 uu____8943 in
                                             let trivial =
                                               let uu____8947 =
                                                 let uu____8952 =
                                                   FStar_All.pipe_right ed2
                                                     FStar_Syntax_Util.get_wp_trivial_combinator in
                                                 FStar_All.pipe_right
                                                   uu____8952 FStar_Util.must in
                                               check_and_gen' "trivial"
                                                 Prims.int_one
                                                 FStar_Pervasives_Native.None
                                                 uu____8947
                                                 (FStar_Pervasives_Native.Some
                                                    k) in
                                             (log_combinator "trivial"
                                                trivial;
                                              trivial)) in
                                  let uu____8964 =
                                    let uu____8981 =
                                      FStar_All.pipe_right ed2
                                        FStar_Syntax_Util.get_eff_repr in
                                    match uu____8981 with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          (ed2.FStar_Syntax_Syntax.actions))
                                    | uu____9010 ->
                                        let repr =
                                          let uu____9014 = fresh_a_and_wp () in
                                          match uu____9014 with
                                          | (a, wp_sort_a) ->
                                              let uu____9027 =
                                                FStar_Syntax_Util.type_u () in
                                              (match uu____9027 with
                                               | (t, uu____9033) ->
                                                   let k =
                                                     let uu____9037 =
                                                       let uu____9046 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a in
                                                       let uu____9053 =
                                                         let uu____9062 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             wp_sort_a in
                                                         [uu____9062] in
                                                       uu____9046 ::
                                                         uu____9053 in
                                                     let uu____9087 =
                                                       FStar_Syntax_Syntax.mk_GTotal
                                                         t in
                                                     FStar_Syntax_Util.arrow
                                                       uu____9037 uu____9087 in
                                                   let uu____9090 =
                                                     let uu____9095 =
                                                       FStar_All.pipe_right
                                                         ed2
                                                         FStar_Syntax_Util.get_eff_repr in
                                                     FStar_All.pipe_right
                                                       uu____9095
                                                       FStar_Util.must in
                                                   check_and_gen' "repr"
                                                     Prims.int_one
                                                     FStar_Pervasives_Native.None
                                                     uu____9090
                                                     (FStar_Pervasives_Native.Some
                                                        k)) in
                                        (log_combinator "repr" repr;
                                         (let mk_repr' t wp =
                                            let uu____9136 =
                                              FStar_TypeChecker_Env.inst_tscheme
                                                repr in
                                            match uu____9136 with
                                            | (uu____9143, repr1) ->
                                                let repr2 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.EraseUniverses;
                                                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                    env repr1 in
                                                let uu____9146 =
                                                  let uu____9147 =
                                                    let uu____9164 =
                                                      let uu____9175 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9192 =
                                                        let uu____9203 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9203] in
                                                      uu____9175 ::
                                                        uu____9192 in
                                                    (repr2, uu____9164) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9147 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9146
                                                  FStar_Range.dummyRange in
                                          let mk_repr a wp =
                                            let uu____9269 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            mk_repr' uu____9269 wp in
                                          let destruct_repr t =
                                            let uu____9284 =
                                              let uu____9285 =
                                                FStar_Syntax_Subst.compress t in
                                              uu____9285.FStar_Syntax_Syntax.n in
                                            match uu____9284 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____9296,
                                                 (t1, uu____9298)::(wp,
                                                                    uu____9300)::[])
                                                -> (t1, wp)
                                            | uu____9359 ->
                                                failwith
                                                  "Unexpected repr type" in
                                          let return_repr =
                                            let return_repr_ts =
                                              let uu____9374 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_return_repr in
                                              FStar_All.pipe_right uu____9374
                                                FStar_Util.must in
                                            let uu____9401 =
                                              fresh_a_and_wp () in
                                            match uu____9401 with
                                            | (a, uu____9409) ->
                                                let x_a =
                                                  let uu____9415 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____9415 in
                                                let res =
                                                  let wp =
                                                    let uu____9420 =
                                                      let uu____9421 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp in
                                                      FStar_All.pipe_right
                                                        uu____9421
                                                        FStar_Pervasives_Native.snd in
                                                    let uu____9430 =
                                                      let uu____9431 =
                                                        let uu____9440 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_All.pipe_right
                                                          uu____9440
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9449 =
                                                        let uu____9460 =
                                                          let uu____9469 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____9469
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9460] in
                                                      uu____9431 ::
                                                        uu____9449 in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____9420 uu____9430
                                                      FStar_Range.dummyRange in
                                                  mk_repr a wp in
                                                let k =
                                                  let uu____9505 =
                                                    let uu____9514 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a in
                                                    let uu____9521 =
                                                      let uu____9530 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          x_a in
                                                      [uu____9530] in
                                                    uu____9514 :: uu____9521 in
                                                  let uu____9555 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res in
                                                  FStar_Syntax_Util.arrow
                                                    uu____9505 uu____9555 in
                                                let uu____9558 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env k in
                                                (match uu____9558 with
                                                 | (k1, uu____9566,
                                                    uu____9567) ->
                                                     let env1 =
                                                       let uu____9571 =
                                                         FStar_TypeChecker_Env.set_range
                                                           env
                                                           (FStar_Pervasives_Native.snd
                                                              return_repr_ts).FStar_Syntax_Syntax.pos in
                                                       FStar_Pervasives_Native.Some
                                                         uu____9571 in
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
                                               let uu____9581 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_bind_repr in
                                               FStar_All.pipe_right
                                                 uu____9581 FStar_Util.must in
                                             let r =
                                               let uu____9619 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_0
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_All.pipe_right
                                                 uu____9619
                                                 FStar_Syntax_Syntax.fv_to_tm in
                                             let uu____9620 =
                                               fresh_a_and_wp () in
                                             match uu____9620 with
                                             | (a, wp_sort_a) ->
                                                 let uu____9633 =
                                                   fresh_a_and_wp () in
                                                 (match uu____9633 with
                                                  | (b, wp_sort_b) ->
                                                      let wp_sort_a_b =
                                                        let uu____9649 =
                                                          let uu____9658 =
                                                            let uu____9665 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____9665 in
                                                          [uu____9658] in
                                                        let uu____9678 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            wp_sort_b in
                                                        FStar_Syntax_Util.arrow
                                                          uu____9649
                                                          uu____9678 in
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
                                                        let uu____9684 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "x_a"
                                                          FStar_Pervasives_Native.None
                                                          uu____9684 in
                                                      let wp_g_x =
                                                        let uu____9686 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g in
                                                        let uu____9687 =
                                                          let uu____9688 =
                                                            let uu____9697 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a in
                                                            FStar_All.pipe_right
                                                              uu____9697
                                                              FStar_Syntax_Syntax.as_arg in
                                                          [uu____9688] in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____9686
                                                          uu____9687
                                                          FStar_Range.dummyRange in
                                                      let res =
                                                        let wp =
                                                          let uu____9726 =
                                                            let uu____9727 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp in
                                                            FStar_All.pipe_right
                                                              uu____9727
                                                              FStar_Pervasives_Native.snd in
                                                          let uu____9736 =
                                                            let uu____9737 =
                                                              let uu____9740
                                                                =
                                                                let uu____9743
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                let uu____9744
                                                                  =
                                                                  let uu____9747
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                  let uu____9748
                                                                    =
                                                                    let uu____9751
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu____9752
                                                                    =
                                                                    let uu____9755
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____9755] in
                                                                    uu____9751
                                                                    ::
                                                                    uu____9752 in
                                                                  uu____9747
                                                                    ::
                                                                    uu____9748 in
                                                                uu____9743 ::
                                                                  uu____9744 in
                                                              r :: uu____9740 in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9737 in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____9726
                                                            uu____9736
                                                            FStar_Range.dummyRange in
                                                        mk_repr b wp in
                                                      let maybe_range_arg =
                                                        let uu____9773 =
                                                          FStar_Util.for_some
                                                            (FStar_Syntax_Util.attr_eq
                                                               FStar_Syntax_Util.dm4f_bind_range_attr)
                                                            ed2.FStar_Syntax_Syntax.eff_attrs in
                                                        if uu____9773
                                                        then
                                                          let uu____9782 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          let uu____9789 =
                                                            let uu____9798 =
                                                              FStar_Syntax_Syntax.null_binder
                                                                FStar_Syntax_Syntax.t_range in
                                                            [uu____9798] in
                                                          uu____9782 ::
                                                            uu____9789
                                                        else [] in
                                                      let k =
                                                        let uu____9833 =
                                                          let uu____9842 =
                                                            let uu____9851 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu____9858 =
                                                              let uu____9867
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  b in
                                                              [uu____9867] in
                                                            uu____9851 ::
                                                              uu____9858 in
                                                          let uu____9892 =
                                                            let uu____9901 =
                                                              let uu____9910
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  wp_f in
                                                              let uu____9917
                                                                =
                                                                let uu____9926
                                                                  =
                                                                  let uu____9933
                                                                    =
                                                                    let uu____9934
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu____9934 in
                                                                  FStar_Syntax_Syntax.null_binder
                                                                    uu____9933 in
                                                                let uu____9935
                                                                  =
                                                                  let uu____9944
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                  let uu____9951
                                                                    =
                                                                    let uu____9960
                                                                    =
                                                                    let uu____9967
                                                                    =
                                                                    let uu____9968
                                                                    =
                                                                    let uu____9977
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____9977] in
                                                                    let uu____9996
                                                                    =
                                                                    let uu____9999
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____9999 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9968
                                                                    uu____9996 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____9967 in
                                                                    [uu____9960] in
                                                                  uu____9944
                                                                    ::
                                                                    uu____9951 in
                                                                uu____9926 ::
                                                                  uu____9935 in
                                                              uu____9910 ::
                                                                uu____9917 in
                                                            FStar_List.append
                                                              maybe_range_arg
                                                              uu____9901 in
                                                          FStar_List.append
                                                            uu____9842
                                                            uu____9892 in
                                                        let uu____10044 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            res in
                                                        FStar_Syntax_Util.arrow
                                                          uu____9833
                                                          uu____10044 in
                                                      let uu____10047 =
                                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                          env k in
                                                      (match uu____10047 with
                                                       | (k1, uu____10055,
                                                          uu____10056) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.set_range
                                                               env
                                                               (FStar_Pervasives_Native.snd
                                                                  bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                           let env2 =
                                                             FStar_All.pipe_right
                                                               (let uu___1009_10066
                                                                  = env1 in
                                                                {
                                                                  FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.solver);
                                                                  FStar_TypeChecker_Env.range
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.range);
                                                                  FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.curmodule);
                                                                  FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.gamma);
                                                                  FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.gamma_sig);
                                                                  FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.gamma_cache);
                                                                  FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.modules);
                                                                  FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.expected_typ);
                                                                  FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.sigtab);
                                                                  FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.attrtab);
                                                                  FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.instantiate_imp);
                                                                  FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.effects);
                                                                  FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.generalize);
                                                                  FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.letrecs);
                                                                  FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.top_level);
                                                                  FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.check_uvars);
                                                                  FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.use_eq);
                                                                  FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.use_eq_strict);
                                                                  FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.is_iface);
                                                                  FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.admit);
                                                                  FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                  FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.lax_universes);
                                                                  FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.phase1);
                                                                  FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.failhard);
                                                                  FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.nosynth);
                                                                  FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.uvar_subtyping);
                                                                  FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.tc_term);
                                                                  FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.type_of);
                                                                  FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.universe_of);
                                                                  FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.check_type_of);
                                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.use_bv_sorts);
                                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                  FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.normalized_eff_names);
                                                                  FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.fv_delta_depths);
                                                                  FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.proof_ns);
                                                                  FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.synth_hook);
                                                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                  FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.splice);
                                                                  FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.mpreprocess);
                                                                  FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.postprocess);
                                                                  FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.identifier_info);
                                                                  FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.tc_hooks);
                                                                  FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.dsenv);
                                                                  FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.nbe);
                                                                  FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.strict_args_tab);
                                                                  FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.erasable_types_tab);
                                                                  FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (
                                                                    uu___1009_10066.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                })
                                                               (fun
                                                                  uu____10067
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____10067) in
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
                                                (let uu____10086 =
                                                   if
                                                     act.FStar_Syntax_Syntax.action_univs
                                                       = []
                                                   then (env, act)
                                                   else
                                                     (let uu____10098 =
                                                        FStar_Syntax_Subst.univ_var_opening
                                                          act.FStar_Syntax_Syntax.action_univs in
                                                      match uu____10098 with
                                                      | (usubst, uvs) ->
                                                          let uu____10121 =
                                                            FStar_TypeChecker_Env.push_univ_vars
                                                              env uvs in
                                                          let uu____10122 =
                                                            let uu___1022_10123
                                                              = act in
                                                            let uu____10124 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_defn in
                                                            let uu____10125 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_typ in
                                                            {
                                                              FStar_Syntax_Syntax.action_name
                                                                =
                                                                (uu___1022_10123.FStar_Syntax_Syntax.action_name);
                                                              FStar_Syntax_Syntax.action_unqualified_name
                                                                =
                                                                (uu___1022_10123.FStar_Syntax_Syntax.action_unqualified_name);
                                                              FStar_Syntax_Syntax.action_univs
                                                                = uvs;
                                                              FStar_Syntax_Syntax.action_params
                                                                =
                                                                (uu___1022_10123.FStar_Syntax_Syntax.action_params);
                                                              FStar_Syntax_Syntax.action_defn
                                                                = uu____10124;
                                                              FStar_Syntax_Syntax.action_typ
                                                                = uu____10125
                                                            } in
                                                          (uu____10121,
                                                            uu____10122)) in
                                                 match uu____10086 with
                                                 | (env1, act1) ->
                                                     let act_typ =
                                                       let uu____10129 =
                                                         let uu____10130 =
                                                           FStar_Syntax_Subst.compress
                                                             act1.FStar_Syntax_Syntax.action_typ in
                                                         uu____10130.FStar_Syntax_Syntax.n in
                                                       match uu____10129 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let c1 =
                                                             FStar_Syntax_Util.comp_to_comp_typ
                                                               c in
                                                           let uu____10156 =
                                                             FStar_Ident.lid_equals
                                                               c1.FStar_Syntax_Syntax.effect_name
                                                               ed2.FStar_Syntax_Syntax.mname in
                                                           if uu____10156
                                                           then
                                                             let uu____10157
                                                               =
                                                               let uu____10160
                                                                 =
                                                                 let uu____10161
                                                                   =
                                                                   let uu____10162
                                                                    =
                                                                    FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                   FStar_Pervasives_Native.fst
                                                                    uu____10162 in
                                                                 mk_repr'
                                                                   c1.FStar_Syntax_Syntax.result_typ
                                                                   uu____10161 in
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 uu____10160 in
                                                             FStar_Syntax_Util.arrow
                                                               bs1
                                                               uu____10157
                                                           else
                                                             act1.FStar_Syntax_Syntax.action_typ
                                                       | uu____10184 ->
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                     let uu____10185 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env1 act_typ in
                                                     (match uu____10185 with
                                                      | (act_typ1,
                                                         uu____10193, g_t) ->
                                                          let env' =
                                                            let uu___1039_10196
                                                              =
                                                              FStar_TypeChecker_Env.set_expected_typ
                                                                env1 act_typ1 in
                                                            {
                                                              FStar_TypeChecker_Env.solver
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.solver);
                                                              FStar_TypeChecker_Env.range
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.range);
                                                              FStar_TypeChecker_Env.curmodule
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.curmodule);
                                                              FStar_TypeChecker_Env.gamma
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.gamma);
                                                              FStar_TypeChecker_Env.gamma_sig
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.gamma_sig);
                                                              FStar_TypeChecker_Env.gamma_cache
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.gamma_cache);
                                                              FStar_TypeChecker_Env.modules
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.modules);
                                                              FStar_TypeChecker_Env.expected_typ
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.expected_typ);
                                                              FStar_TypeChecker_Env.sigtab
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.sigtab);
                                                              FStar_TypeChecker_Env.attrtab
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.attrtab);
                                                              FStar_TypeChecker_Env.instantiate_imp
                                                                = false;
                                                              FStar_TypeChecker_Env.effects
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.effects);
                                                              FStar_TypeChecker_Env.generalize
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.generalize);
                                                              FStar_TypeChecker_Env.letrecs
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.letrecs);
                                                              FStar_TypeChecker_Env.top_level
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.top_level);
                                                              FStar_TypeChecker_Env.check_uvars
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.check_uvars);
                                                              FStar_TypeChecker_Env.use_eq
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.use_eq);
                                                              FStar_TypeChecker_Env.use_eq_strict
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.use_eq_strict);
                                                              FStar_TypeChecker_Env.is_iface
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.is_iface);
                                                              FStar_TypeChecker_Env.admit
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.admit);
                                                              FStar_TypeChecker_Env.lax
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.lax);
                                                              FStar_TypeChecker_Env.lax_universes
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.lax_universes);
                                                              FStar_TypeChecker_Env.phase1
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.phase1);
                                                              FStar_TypeChecker_Env.failhard
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.failhard);
                                                              FStar_TypeChecker_Env.nosynth
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.nosynth);
                                                              FStar_TypeChecker_Env.uvar_subtyping
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.uvar_subtyping);
                                                              FStar_TypeChecker_Env.tc_term
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.tc_term);
                                                              FStar_TypeChecker_Env.type_of
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.type_of);
                                                              FStar_TypeChecker_Env.universe_of
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.universe_of);
                                                              FStar_TypeChecker_Env.check_type_of
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.check_type_of);
                                                              FStar_TypeChecker_Env.use_bv_sorts
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.use_bv_sorts);
                                                              FStar_TypeChecker_Env.qtbl_name_and_index
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                              FStar_TypeChecker_Env.normalized_eff_names
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.normalized_eff_names);
                                                              FStar_TypeChecker_Env.fv_delta_depths
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.fv_delta_depths);
                                                              FStar_TypeChecker_Env.proof_ns
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.proof_ns);
                                                              FStar_TypeChecker_Env.synth_hook
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.synth_hook);
                                                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                              FStar_TypeChecker_Env.splice
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.splice);
                                                              FStar_TypeChecker_Env.mpreprocess
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.mpreprocess);
                                                              FStar_TypeChecker_Env.postprocess
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.postprocess);
                                                              FStar_TypeChecker_Env.identifier_info
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.identifier_info);
                                                              FStar_TypeChecker_Env.tc_hooks
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.tc_hooks);
                                                              FStar_TypeChecker_Env.dsenv
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.dsenv);
                                                              FStar_TypeChecker_Env.nbe
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.nbe);
                                                              FStar_TypeChecker_Env.strict_args_tab
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.strict_args_tab);
                                                              FStar_TypeChecker_Env.erasable_types_tab
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.erasable_types_tab);
                                                              FStar_TypeChecker_Env.enable_defer_to_tac
                                                                =
                                                                (uu___1039_10196.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                            } in
                                                          ((let uu____10198 =
                                                              FStar_TypeChecker_Env.debug
                                                                env1
                                                                (FStar_Options.Other
                                                                   "ED") in
                                                            if uu____10198
                                                            then
                                                              let uu____10199
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  act1.FStar_Syntax_Syntax.action_name in
                                                              let uu____10200
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act1.FStar_Syntax_Syntax.action_defn in
                                                              let uu____10201
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ1 in
                                                              FStar_Util.print3
                                                                "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                uu____10199
                                                                uu____10200
                                                                uu____10201
                                                            else ());
                                                           (let uu____10203 =
                                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                env'
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            match uu____10203
                                                            with
                                                            | (act_defn,
                                                               uu____10211,
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
                                                                let uu____10215
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
                                                                    let uu____10251
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10251
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10263)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10270
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10270 in
                                                                    let uu____10273
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10273
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10287,
                                                                    g) ->
                                                                    (k1, g)))
                                                                  | uu____10291
                                                                    ->
                                                                    let uu____10292
                                                                    =
                                                                    let uu____10297
                                                                    =
                                                                    let uu____10298
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10299
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10298
                                                                    uu____10299 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10297) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10292
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                (match uu____10215
                                                                 with
                                                                 | (expected_k,
                                                                    g_k) ->
                                                                    let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    ((
                                                                    let uu____10314
                                                                    =
                                                                    let uu____10315
                                                                    =
                                                                    let uu____10316
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10316 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10315 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10314);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu____10318
                                                                    =
                                                                    let uu____10319
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10319.FStar_Syntax_Syntax.n in
                                                                    match uu____10318
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10344
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10344
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10351
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10351
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10371
                                                                    =
                                                                    let uu____10372
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10372] in
                                                                    let uu____10373
                                                                    =
                                                                    let uu____10384
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10384] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10371;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10373;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10409
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10409))
                                                                    | 
                                                                    uu____10412
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10413
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10433
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10433)) in
                                                                    match uu____10413
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
                                                                    let uu___1089_10452
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1089_10452.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1089_10452.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1089_10452.FStar_Syntax_Syntax.action_params);
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
                                  match uu____8964 with
                                  | (repr, return_repr, bind_repr, actions)
                                      ->
                                      let cl ts =
                                        let ts1 =
                                          FStar_Syntax_Subst.close_tscheme
                                            ed_bs ts in
                                        let ed_univs_closing =
                                          FStar_Syntax_Subst.univ_var_closing
                                            ed_univs in
                                        let uu____10495 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length ed_bs)
                                            ed_univs_closing in
                                        FStar_Syntax_Subst.subst_tscheme
                                          uu____10495 ts1 in
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
                                            uu____10507 ->
                                            FStar_Syntax_Syntax.Primitive_eff
                                              combinators1
                                        | FStar_Syntax_Syntax.DM4F_eff
                                            uu____10508 ->
                                            FStar_Syntax_Syntax.DM4F_eff
                                              combinators1
                                        | uu____10509 ->
                                            failwith
                                              "Impossible! tc_eff_decl on a layered effect is not expected" in
                                      let ed3 =
                                        let uu___1109_10511 = ed2 in
                                        let uu____10512 = cl signature in
                                        let uu____10513 =
                                          FStar_List.map
                                            (fun a ->
                                               let uu___1112_10521 = a in
                                               let uu____10522 =
                                                 let uu____10523 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_defn)) in
                                                 FStar_All.pipe_right
                                                   uu____10523
                                                   FStar_Pervasives_Native.snd in
                                               let uu____10548 =
                                                 let uu____10549 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_typ)) in
                                                 FStar_All.pipe_right
                                                   uu____10549
                                                   FStar_Pervasives_Native.snd in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___1112_10521.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___1112_10521.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   =
                                                   (uu___1112_10521.FStar_Syntax_Syntax.action_univs);
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___1112_10521.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = uu____10522;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____10548
                                               }) actions in
                                        {
                                          FStar_Syntax_Syntax.mname =
                                            (uu___1109_10511.FStar_Syntax_Syntax.mname);
                                          FStar_Syntax_Syntax.cattributes =
                                            (uu___1109_10511.FStar_Syntax_Syntax.cattributes);
                                          FStar_Syntax_Syntax.univs =
                                            (uu___1109_10511.FStar_Syntax_Syntax.univs);
                                          FStar_Syntax_Syntax.binders =
                                            (uu___1109_10511.FStar_Syntax_Syntax.binders);
                                          FStar_Syntax_Syntax.signature =
                                            uu____10512;
                                          FStar_Syntax_Syntax.combinators =
                                            combinators2;
                                          FStar_Syntax_Syntax.actions =
                                            uu____10513;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            (uu___1109_10511.FStar_Syntax_Syntax.eff_attrs)
                                        } in
                                      ((let uu____10575 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "ED") in
                                        if uu____10575
                                        then
                                          let uu____10576 =
                                            FStar_Syntax_Print.eff_decl_to_string
                                              false ed3 in
                                          FStar_Util.print1
                                            "Typechecked effect declaration:\n\t%s\n"
                                            uu____10576
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
          let uu____10606 =
            let uu____10627 =
              FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
            if uu____10627
            then tc_layered_eff_decl
            else tc_non_layered_eff_decl in
          uu____10606 env ed quals attrs
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
        let fail uu____10677 =
          let uu____10678 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____10683 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____10678 uu____10683 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____10727)::(wp, uu____10729)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____10758 -> fail ())
        | uu____10759 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____10771 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____10771
       then
         let uu____10772 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____10772
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____10786 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____10786.FStar_Syntax_Syntax.pos in
       let uu____10795 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____10795 with
       | (us, lift, lift_ty) ->
           ((let uu____10806 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____10806
             then
               let uu____10807 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____10812 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____10807 uu____10812
             else ());
            (let uu____10818 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____10818 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____10833 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____10834 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____10835 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____10833 uu____10834 s uu____10835 in
                   let uu____10836 =
                     let uu____10843 =
                       let uu____10848 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____10848
                         (fun uu____10865 ->
                            match uu____10865 with
                            | (t, u) ->
                                let uu____10876 =
                                  let uu____10877 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____10877
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____10876, u)) in
                     match uu____10843 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____10895 =
                             let uu____10896 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____10896.FStar_Syntax_Syntax.n in
                           match uu____10895 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____10908)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____10935 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____10935 with
                                | (a', uu____10945)::bs1 ->
                                    let uu____10965 =
                                      let uu____10966 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____10966
                                        FStar_Pervasives_Native.fst in
                                    let uu____11031 =
                                      let uu____11044 =
                                        let uu____11047 =
                                          let uu____11048 =
                                            let uu____11055 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11055) in
                                          FStar_Syntax_Syntax.NT uu____11048 in
                                        [uu____11047] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11044 in
                                    FStar_All.pipe_right uu____10965
                                      uu____11031)
                           | uu____11070 ->
                               let uu____11071 =
                                 let uu____11076 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11076) in
                               FStar_Errors.raise_error uu____11071 r in
                         let uu____11085 =
                           let uu____11096 =
                             let uu____11101 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11108 =
                               let uu____11109 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11109
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11101 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11108 in
                           match uu____11096 with
                           | (f_sort, g) ->
                               let uu____11130 =
                                 let uu____11137 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11137
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11130, g) in
                         (match uu____11085 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11203 =
                                let uu____11208 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11209 =
                                  let uu____11210 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11210
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11208 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11209 in
                              (match uu____11203 with
                               | (repr, g_repr) ->
                                   let uu____11227 =
                                     let uu____11232 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11233 =
                                       let uu____11234 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11235 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11234 uu____11235 in
                                     pure_wp_uvar uu____11232 repr
                                       uu____11233 r in
                                   (match uu____11227 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11245 =
                                            let uu____11246 =
                                              let uu____11247 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11247] in
                                            let uu____11248 =
                                              let uu____11259 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11259] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11246;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11248;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11245 in
                                        let uu____11292 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11295 =
                                          let uu____11296 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11296 guard_wp in
                                        (uu____11292, uu____11295)))) in
                   match uu____10836 with
                   | (k, g_k) ->
                       ((let uu____11306 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11306
                         then
                           let uu____11307 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11307
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11313 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11313
                          then
                            let uu____11314 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11314
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          let check_non_informative_binders =
                            (FStar_TypeChecker_Env.is_reifiable_effect env
                               sub.FStar_Syntax_Syntax.target)
                              &&
                              (let uu____11319 =
                                 FStar_TypeChecker_Env.fv_with_lid_has_attr
                                   env sub.FStar_Syntax_Syntax.target
                                   FStar_Parser_Const.allow_informative_binders_attr in
                               Prims.op_Negation uu____11319) in
                          (let uu____11321 =
                             let uu____11322 = FStar_Syntax_Subst.compress k1 in
                             uu____11322.FStar_Syntax_Syntax.n in
                           match uu____11321 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11347 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11347 with
                                | (a::bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11378 =
                                      let uu____11397 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11397
                                        (fun uu____11472 ->
                                           match uu____11472 with
                                           | (l1, l2) ->
                                               let uu____11545 =
                                                 FStar_List.hd l2 in
                                               (l1, uu____11545)) in
                                    (match uu____11378 with
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
                             let uu___1222_11618 = sub in
                             let uu____11619 =
                               let uu____11622 =
                                 let uu____11623 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____11623) in
                               FStar_Pervasives_Native.Some uu____11622 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1222_11618.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1222_11618.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____11619;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____11637 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____11637
                            then
                              let uu____11638 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____11638
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
          let uu____11671 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____11671 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____11674 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____11674
        then tc_layered_lift env sub
        else
          (let uu____11676 =
             let uu____11683 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____11683 in
           match uu____11676 with
           | (a, wp_a_src) ->
               let uu____11690 =
                 let uu____11697 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____11697 in
               (match uu____11690 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____11705 =
                        let uu____11708 =
                          let uu____11709 =
                            let uu____11716 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____11716) in
                          FStar_Syntax_Syntax.NT uu____11709 in
                        [uu____11708] in
                      FStar_Syntax_Subst.subst uu____11705 wp_b_tgt in
                    let expected_k =
                      let uu____11724 =
                        let uu____11733 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____11740 =
                          let uu____11749 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____11749] in
                        uu____11733 :: uu____11740 in
                      let uu____11774 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____11724 uu____11774 in
                    let repr_type eff_name a1 wp =
                      (let uu____11796 =
                         let uu____11797 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____11797 in
                       if uu____11796
                       then
                         let uu____11798 =
                           let uu____11803 =
                             let uu____11804 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____11804 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____11803) in
                         let uu____11805 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____11798 uu____11805
                       else ());
                      (let uu____11807 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____11807 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____11839 =
                               let uu____11840 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____11840
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____11839 in
                           let uu____11847 =
                             let uu____11848 =
                               let uu____11865 =
                                 let uu____11876 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____11885 =
                                   let uu____11896 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____11896] in
                                 uu____11876 :: uu____11885 in
                               (repr, uu____11865) in
                             FStar_Syntax_Syntax.Tm_app uu____11848 in
                           let uu____11941 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____11847 uu____11941) in
                    let uu____11942 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12114 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12123 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12123 with
                              | (usubst, uvs1) ->
                                  let uu____12146 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12147 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12146, uu____12147)
                            else (env, lift_wp) in
                          (match uu____12114 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12192 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12192)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12263 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12276 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12276 with
                              | (usubst, uvs) ->
                                  let uu____12301 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12301)
                            else ([], lift) in
                          (match uu____12263 with
                           | (uvs, lift1) ->
                               ((let uu____12336 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12336
                                 then
                                   let uu____12337 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12337
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12340 =
                                   let uu____12347 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12347 lift1 in
                                 match uu____12340 with
                                 | (lift2, comp, uu____12372) ->
                                     let uu____12373 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12373 with
                                      | (uu____12402, lift_wp, lift_elab) ->
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
                                            let uu____12429 =
                                              let uu____12440 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____12440 in
                                            let uu____12457 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____12429, uu____12457)
                                          else
                                            (let uu____12485 =
                                               let uu____12496 =
                                                 let uu____12505 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____12505) in
                                               FStar_Pervasives_Native.Some
                                                 uu____12496 in
                                             let uu____12520 =
                                               let uu____12529 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____12529) in
                                             (uu____12485, uu____12520)))))) in
                    (match uu____11942 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1306_12593 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1306_12593.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1306_12593.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1306_12593.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1306_12593.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1306_12593.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1306_12593.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1306_12593.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1306_12593.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1306_12593.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1306_12593.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1306_12593.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1306_12593.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1306_12593.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1306_12593.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1306_12593.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1306_12593.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1306_12593.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1306_12593.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1306_12593.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1306_12593.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1306_12593.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1306_12593.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1306_12593.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1306_12593.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1306_12593.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1306_12593.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1306_12593.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1306_12593.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1306_12593.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1306_12593.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1306_12593.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1306_12593.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1306_12593.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1306_12593.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1306_12593.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1306_12593.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1306_12593.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1306_12593.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1306_12593.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1306_12593.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1306_12593.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1306_12593.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1306_12593.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1306_12593.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1306_12593.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1306_12593.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____12625 =
                                 let uu____12630 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____12630 with
                                 | (usubst, uvs1) ->
                                     let uu____12653 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____12654 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____12653, uu____12654) in
                               (match uu____12625 with
                                | (env2, lift2) ->
                                    let uu____12659 =
                                      let uu____12666 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____12666 in
                                    (match uu____12659 with
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
                                             let uu____12692 =
                                               let uu____12693 =
                                                 let uu____12710 =
                                                   let uu____12721 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____12730 =
                                                     let uu____12741 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____12741] in
                                                   uu____12721 :: uu____12730 in
                                                 (lift_wp1, uu____12710) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____12693 in
                                             let uu____12786 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____12692 uu____12786 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____12790 =
                                             let uu____12799 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____12806 =
                                               let uu____12815 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____12822 =
                                                 let uu____12831 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____12831] in
                                               uu____12815 :: uu____12822 in
                                             uu____12799 :: uu____12806 in
                                           let uu____12862 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____12790 uu____12862 in
                                         let uu____12865 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____12865 with
                                          | (expected_k2, uu____12875,
                                             uu____12876) ->
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
                                                   let uu____12880 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____12880)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____12888 =
                             let uu____12889 =
                               let uu____12890 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____12890
                                 FStar_List.length in
                             uu____12889 <> Prims.int_one in
                           if uu____12888
                           then
                             let uu____12909 =
                               let uu____12914 =
                                 let uu____12915 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12916 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12917 =
                                   let uu____12918 =
                                     let uu____12919 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12919
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12918
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12915 uu____12916 uu____12917 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12914) in
                             FStar_Errors.raise_error uu____12909 r
                           else ());
                          (let uu____12940 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____12942 =
                                  let uu____12943 =
                                    let uu____12946 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____12946
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____12943
                                    FStar_List.length in
                                uu____12942 <> Prims.int_one) in
                           if uu____12940
                           then
                             let uu____12981 =
                               let uu____12986 =
                                 let uu____12987 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12988 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12989 =
                                   let uu____12990 =
                                     let uu____12991 =
                                       let uu____12994 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____12994
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12991
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12990
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12987 uu____12988 uu____12989 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12986) in
                             FStar_Errors.raise_error uu____12981 r
                           else ());
                          (let uu___1343_13030 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1343_13030.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1343_13030.FStar_Syntax_Syntax.target);
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
    fun uu____13060 ->
      fun r ->
        match uu____13060 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13083 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13107 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13107 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13138 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13138 c in
                     let uu____13147 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13147, uvs1, tps1, c1)) in
            (match uu____13083 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13167 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13167 with
                  | (tps2, c2) ->
                      let uu____13182 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13182 with
                       | (tps3, env3, us) ->
                           let uu____13200 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13200 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13226)::uu____13227 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13246 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13252 =
                                    let uu____13253 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13253 in
                                  if uu____13252
                                  then
                                    let uu____13254 =
                                      let uu____13259 =
                                        let uu____13260 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13261 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13260 uu____13261 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13259) in
                                    FStar_Errors.raise_error uu____13254 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13265 =
                                    let uu____13266 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____13266 in
                                  match uu____13265 with
                                  | (uvs2, t) ->
                                      let uu____13295 =
                                        let uu____13300 =
                                          let uu____13313 =
                                            let uu____13314 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13314.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13313) in
                                        match uu____13300 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13329, c5)) -> ([], c5)
                                        | (uu____13371,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____13410 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13295 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____13438 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____13438 with
                                               | (uu____13443, t1) ->
                                                   let uu____13445 =
                                                     let uu____13450 =
                                                       let uu____13451 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____13452 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____13453 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____13451
                                                         uu____13452
                                                         uu____13453 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____13450) in
                                                   FStar_Errors.raise_error
                                                     uu____13445 r)
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
              let uu____13489 =
                let uu____13490 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13490 FStar_Ident.string_of_id in
              let uu____13491 =
                let uu____13492 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13492 FStar_Ident.string_of_id in
              let uu____13493 =
                let uu____13494 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13494 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____13489 uu____13491
                uu____13493 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____13500 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____13500 with
            | (us, t, ty) ->
                let uu____13514 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____13514 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____13527 =
                         let uu____13532 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____13532
                           (fun uu____13549 ->
                              match uu____13549 with
                              | (t1, u) ->
                                  let uu____13560 =
                                    let uu____13561 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____13561
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____13560, u)) in
                       match uu____13527 with
                       | (a, u_a) ->
                           let uu____13568 =
                             let uu____13573 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____13573
                               (fun uu____13590 ->
                                  match uu____13590 with
                                  | (t1, u) ->
                                      let uu____13601 =
                                        let uu____13602 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____13602
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13601, u)) in
                           (match uu____13568 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____13618 =
                                    let uu____13619 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____13619.FStar_Syntax_Syntax.n in
                                  match uu____13618 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____13631) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____13658 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____13658 with
                                       | (a', uu____13668)::(b', uu____13670)::bs1
                                           ->
                                           let uu____13700 =
                                             let uu____13701 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____13701
                                               FStar_Pervasives_Native.fst in
                                           let uu____13766 =
                                             let uu____13779 =
                                               let uu____13782 =
                                                 let uu____13783 =
                                                   let uu____13790 =
                                                     let uu____13793 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____13793
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____13790) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____13783 in
                                               let uu____13806 =
                                                 let uu____13809 =
                                                   let uu____13810 =
                                                     let uu____13817 =
                                                       let uu____13820 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____13820
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____13817) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____13810 in
                                                 [uu____13809] in
                                               uu____13782 :: uu____13806 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____13779 in
                                           FStar_All.pipe_right uu____13700
                                             uu____13766)
                                  | uu____13841 ->
                                      let uu____13842 =
                                        let uu____13847 =
                                          let uu____13848 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____13849 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____13848 uu____13849 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____13847) in
                                      FStar_Errors.raise_error uu____13842 r in
                                let bs = a :: b :: rest_bs in
                                let uu____13879 =
                                  let uu____13890 =
                                    let uu____13895 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____13896 =
                                      let uu____13897 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____13897
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____13895 r m u_a uu____13896 in
                                  match uu____13890 with
                                  | (repr, g) ->
                                      let uu____13918 =
                                        let uu____13925 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____13925
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13918, g) in
                                (match uu____13879 with
                                 | (f, guard_f) ->
                                     let uu____13956 =
                                       let x_a =
                                         let uu____13974 =
                                           let uu____13975 =
                                             let uu____13976 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____13976
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____13975 in
                                         FStar_All.pipe_right uu____13974
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____13991 =
                                         let uu____13996 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____14015 =
                                           let uu____14016 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____14016
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____13996 r n u_b uu____14015 in
                                       match uu____13991 with
                                       | (repr, g) ->
                                           let uu____14037 =
                                             let uu____14044 =
                                               let uu____14045 =
                                                 let uu____14046 =
                                                   let uu____14049 =
                                                     let uu____14052 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14052 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14049 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14046 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14045 in
                                             FStar_All.pipe_right uu____14044
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____14037, g) in
                                     (match uu____13956 with
                                      | (g, guard_g) ->
                                          let uu____14095 =
                                            let uu____14100 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14101 =
                                              let uu____14102 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14102
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14100 r p u_b uu____14101 in
                                          (match uu____14095 with
                                           | (repr, guard_repr) ->
                                               let uu____14117 =
                                                 let uu____14122 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14123 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14122
                                                   repr uu____14123 r in
                                               (match uu____14117 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14133 =
                                                        let uu____14136 =
                                                          let uu____14137 =
                                                            let uu____14138 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14138] in
                                                          let uu____14139 =
                                                            let uu____14150 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14150] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14137;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14139;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14136 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14133 in
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
                                                     (let uu____14210 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14210
                                                      then
                                                        let uu____14211 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14216 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14211
                                                          uu____14216
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
                                                          (let uu____14225 =
                                                             FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                               env1 p
                                                               FStar_Parser_Const.allow_informative_binders_attr in
                                                           Prims.op_Negation
                                                             uu____14225) in
                                                      (let uu____14227 =
                                                         let uu____14228 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14228.FStar_Syntax_Syntax.n in
                                                       match uu____14227 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14253 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14253
                                                            with
                                                            | (a1::b1::bs2,
                                                               c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14297
                                                                  =
                                                                  let uu____14324
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____14324
                                                                    (
                                                                    fun
                                                                    uu____14408
                                                                    ->
                                                                    match uu____14408
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____14489
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____14516
                                                                    =
                                                                    let uu____14523
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____14523
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____14489,
                                                                    uu____14516)) in
                                                                (match uu____14297
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____14638
                                                                    =
                                                                    let uu____14639
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____14639.FStar_Syntax_Syntax.n in
                                                                    match uu____14638
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____14644,
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
                                                      (let uu____14688 =
                                                         let uu____14693 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____14693) in
                                                       FStar_Errors.log_issue
                                                         r uu____14688);
                                                      (let uu____14694 =
                                                         let uu____14695 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____14695) in
                                                       ((us1, t),
                                                         uu____14694))))))))))))
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
            let uu____14742 =
              let uu____14743 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____14743 FStar_Ident.string_of_id in
            let uu____14744 =
              let uu____14745 =
                let uu____14746 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14746 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____14745 in
            Prims.op_Hat uu____14742 uu____14744 in
          let uu____14747 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____14747 with
          | (us, t, ty) ->
              let uu____14761 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____14761 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____14774 =
                       let uu____14779 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____14779
                         (fun uu____14796 ->
                            match uu____14796 with
                            | (t1, u) ->
                                let uu____14807 =
                                  let uu____14808 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____14808
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____14807, u)) in
                     match uu____14774 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____14824 =
                             let uu____14825 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____14825.FStar_Syntax_Syntax.n in
                           match uu____14824 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____14837)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____14864 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____14864 with
                                | (a', uu____14874)::bs1 ->
                                    let uu____14894 =
                                      let uu____14895 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____14895
                                        FStar_Pervasives_Native.fst in
                                    let uu____14992 =
                                      let uu____15005 =
                                        let uu____15008 =
                                          let uu____15009 =
                                            let uu____15016 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____15016) in
                                          FStar_Syntax_Syntax.NT uu____15009 in
                                        [uu____15008] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____15005 in
                                    FStar_All.pipe_right uu____14894
                                      uu____14992)
                           | uu____15031 ->
                               let uu____15032 =
                                 let uu____15037 =
                                   let uu____15038 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____15039 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____15038 uu____15039 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____15037) in
                               FStar_Errors.raise_error uu____15032 r in
                         let bs = a :: rest_bs in
                         let uu____15063 =
                           let uu____15074 =
                             let uu____15079 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15080 =
                               let uu____15081 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15081
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15079 r m u uu____15080 in
                           match uu____15074 with
                           | (repr, g) ->
                               let uu____15102 =
                                 let uu____15109 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15109
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15102, g) in
                         (match uu____15063 with
                          | (f, guard_f) ->
                              let uu____15140 =
                                let uu____15145 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15146 =
                                  let uu____15147 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15147
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15145 r n u uu____15146 in
                              (match uu____15140 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15162 =
                                     let uu____15167 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15168 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15167 ret_t
                                       uu____15168 r in
                                   (match uu____15162 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15176 =
                                            let uu____15177 =
                                              let uu____15178 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15178] in
                                            let uu____15179 =
                                              let uu____15190 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15190] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15177;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15179;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15176 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15245 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15245
                                          then
                                            let uu____15246 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15246
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
                                             let uu____15253 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15253
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15257 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15257
                                            then
                                              let uu____15258 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15258
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu____15266 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation
                                                   uu____15266) in
                                            (let uu____15268 =
                                               let uu____15269 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____15269.FStar_Syntax_Syntax.n in
                                             match uu____15268 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu____15294 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu____15294 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu____15325 =
                                                        let uu____15344 =
                                                          FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_All.pipe_right
                                                          uu____15344
                                                          (fun uu____15419 ->
                                                             match uu____15419
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu____15492
                                                                   =
                                                                   FStar_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu____15492)) in
                                                      (match uu____15325 with
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
                                            (let uu____15565 =
                                               let uu____15570 =
                                                 FStar_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu____15570) in
                                             FStar_Errors.log_issue r
                                               uu____15565);
                                            (let uu____15571 =
                                               let uu____15572 =
                                                 FStar_All.pipe_right k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu____15572) in
                                             ((us1, t), uu____15571))))))))))))