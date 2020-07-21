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
                   let uu____3190 =
                     let uu____3191 =
                       let uu____3194 =
                         FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____3194
                         FStar_Syntax_Subst.compress in
                     uu____3191.FStar_Syntax_Syntax.n in
                   match uu____3190 with
                   | FStar_Syntax_Syntax.Tm_unknown ->
                       let signature_ts =
                         let uu____3206 = signature in
                         match uu____3206 with
                         | (us, t, uu____3221) -> (us, t) in
                       let uu____3238 =
                         FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                           [FStar_Syntax_Syntax.U_unknown] in
                       (match uu____3238 with
                        | (uu____3247, signature_t) ->
                            let uu____3249 =
                              let uu____3250 =
                                FStar_Syntax_Subst.compress signature_t in
                              uu____3250.FStar_Syntax_Syntax.n in
                            (match uu____3249 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3258)
                                 ->
                                 let bs1 = FStar_Syntax_Subst.open_binders bs in
                                 let repr_t =
                                   let repr_ts =
                                     let uu____3284 = repr in
                                     match uu____3284 with
                                     | (us, t, uu____3299) -> (us, t) in
                                   let uu____3316 =
                                     FStar_TypeChecker_Env.inst_tscheme_with
                                       repr_ts
                                       [FStar_Syntax_Syntax.U_unknown] in
                                   FStar_All.pipe_right uu____3316
                                     FStar_Pervasives_Native.snd in
                                 let repr_t_applied =
                                   let uu____3330 =
                                     let uu____3331 =
                                       let uu____3348 =
                                         let uu____3359 =
                                           let uu____3362 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst) in
                                           FStar_All.pipe_right uu____3362
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name) in
                                         FStar_All.pipe_right uu____3359
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.as_arg) in
                                       (repr_t, uu____3348) in
                                     FStar_Syntax_Syntax.Tm_app uu____3331 in
                                   FStar_Syntax_Syntax.mk uu____3330
                                     FStar_Range.dummyRange in
                                 let f_b =
                                   FStar_Syntax_Syntax.null_binder
                                     repr_t_applied in
                                 let uu____3412 =
                                   let uu____3413 =
                                     let uu____3416 =
                                       FStar_All.pipe_right f_b
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____3416
                                       FStar_Syntax_Syntax.bv_to_name in
                                   FStar_Syntax_Util.abs
                                     (FStar_List.append bs1 [f_b]) uu____3413
                                     FStar_Pervasives_Native.None in
                                 ([], uu____3412)
                             | uu____3445 -> failwith "Impossible!"))
                   | uu____3450 -> ts in
                 let r =
                   (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
                 let uu____3452 =
                   check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
                 match uu____3452 with
                 | (stronger_us, stronger_t, stronger_ty) ->
                     ((let uu____3475 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "LayeredEffectsTc") in
                       if uu____3475
                       then
                         let uu____3476 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_t) in
                         let uu____3481 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_ty) in
                         FStar_Util.print2
                           "stronger combinator typechecked with term: %s and type: %s\n"
                           uu____3476 uu____3481
                       else ());
                      (let uu____3487 =
                         FStar_Syntax_Subst.open_univ_vars stronger_us
                           stronger_ty in
                       match uu____3487 with
                       | (us, ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____3508 = fresh_a_and_u_a "a" in
                             match uu____3508 with
                             | (a, u) ->
                                 let rest_bs =
                                   let uu____3536 =
                                     let uu____3537 =
                                       FStar_Syntax_Subst.compress ty in
                                     uu____3537.FStar_Syntax_Syntax.n in
                                   match uu____3536 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs, uu____3549) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____3576 =
                                         FStar_Syntax_Subst.open_binders bs in
                                       (match uu____3576 with
                                        | (a', uu____3586)::bs1 ->
                                            let uu____3606 =
                                              let uu____3607 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one)) in
                                              FStar_All.pipe_right uu____3607
                                                FStar_Pervasives_Native.fst in
                                            let uu____3704 =
                                              let uu____3717 =
                                                let uu____3720 =
                                                  let uu____3721 =
                                                    let uu____3728 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           a) in
                                                    (a', uu____3728) in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3721 in
                                                [uu____3720] in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____3717 in
                                            FStar_All.pipe_right uu____3606
                                              uu____3704)
                                   | uu____3743 ->
                                       not_an_arrow_error "stronger"
                                         (Prims.of_int (2)) ty r in
                                 let bs = a :: rest_bs in
                                 let uu____3759 =
                                   let uu____3770 =
                                     let uu____3775 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____3776 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name in
                                     fresh_repr r uu____3775 u uu____3776 in
                                   match uu____3770 with
                                   | (repr1, g) ->
                                       let uu____3791 =
                                         let uu____3798 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr1 in
                                         FStar_All.pipe_right uu____3798
                                           FStar_Syntax_Syntax.mk_binder in
                                       (uu____3791, g) in
                                 (match uu____3759 with
                                  | (f, guard_f) ->
                                      let uu____3837 =
                                        let uu____3842 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____3843 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____3842 u uu____3843 in
                                      (match uu____3837 with
                                       | (ret_t, guard_ret_t) ->
                                           let uu____3860 =
                                             let uu____3865 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3866 =
                                               let uu____3867 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               FStar_Util.format1
                                                 "implicit for pure_wp in checking stronger for %s"
                                                 uu____3867 in
                                             pure_wp_uvar uu____3865 ret_t
                                               uu____3866 r in
                                           (match uu____3860 with
                                            | (pure_wp_uvar1, guard_wp) ->
                                                let c =
                                                  let uu____3883 =
                                                    let uu____3884 =
                                                      let uu____3885 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          () in
                                                      [uu____3885] in
                                                    let uu____3886 =
                                                      let uu____3897 =
                                                        FStar_All.pipe_right
                                                          pure_wp_uvar1
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____3897] in
                                                    {
                                                      FStar_Syntax_Syntax.comp_univs
                                                        = uu____3884;
                                                      FStar_Syntax_Syntax.effect_name
                                                        =
                                                        FStar_Parser_Const.effect_PURE_lid;
                                                      FStar_Syntax_Syntax.result_typ
                                                        = ret_t;
                                                      FStar_Syntax_Syntax.effect_args
                                                        = uu____3886;
                                                      FStar_Syntax_Syntax.flags
                                                        = []
                                                    } in
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    uu____3883 in
                                                let k =
                                                  FStar_Syntax_Util.arrow
                                                    (FStar_List.append bs [f])
                                                    c in
                                                ((let uu____3952 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env)
                                                      (FStar_Options.Other
                                                         "LayeredEffectsTc") in
                                                  if uu____3952
                                                  then
                                                    let uu____3953 =
                                                      FStar_Syntax_Print.term_to_string
                                                        k in
                                                    FStar_Util.print1
                                                      "Expected type of subcomp before unification: %s\n"
                                                      uu____3953
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
                                                     let uu____3958 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____3958
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   (let uu____3960 =
                                                      let uu____3961 =
                                                        FStar_Syntax_Subst.compress
                                                          k1 in
                                                      uu____3961.FStar_Syntax_Syntax.n in
                                                    match uu____3960 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs1, c1) ->
                                                        let uu____3986 =
                                                          FStar_Syntax_Subst.open_comp
                                                            bs1 c1 in
                                                        (match uu____3986
                                                         with
                                                         | (a1::bs2, c2) ->
                                                             let res_t =
                                                               FStar_Syntax_Util.comp_result
                                                                 c2 in
                                                             let uu____4017 =
                                                               let uu____4036
                                                                 =
                                                                 FStar_List.splitAt
                                                                   ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                   bs2 in
                                                               FStar_All.pipe_right
                                                                 uu____4036
                                                                 (fun
                                                                    uu____4111
                                                                    ->
                                                                    match uu____4111
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____4184
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu____4184)) in
                                                             (match uu____4017
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
                                                   (let uu____4256 =
                                                      FStar_All.pipe_right k1
                                                        (FStar_Syntax_Subst.close_univ_vars
                                                           stronger_us) in
                                                    (stronger_us, stronger_t,
                                                      uu____4256)))))))))))) in
               log_combinator "stronger_repr" stronger_repr;
               (let if_then_else =
                  let if_then_else_ts =
                    let ts =
                      let uu____4291 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____4291 FStar_Util.must in
                    let uu____4318 =
                      let uu____4319 =
                        let uu____4322 =
                          FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                        FStar_All.pipe_right uu____4322
                          FStar_Syntax_Subst.compress in
                      uu____4319.FStar_Syntax_Syntax.n in
                    match uu____4318 with
                    | FStar_Syntax_Syntax.Tm_unknown ->
                        let signature_ts =
                          let uu____4334 = signature in
                          match uu____4334 with
                          | (us, t, uu____4349) -> (us, t) in
                        let uu____4366 =
                          FStar_TypeChecker_Env.inst_tscheme_with
                            signature_ts [FStar_Syntax_Syntax.U_unknown] in
                        (match uu____4366 with
                         | (uu____4375, signature_t) ->
                             let uu____4377 =
                               let uu____4378 =
                                 FStar_Syntax_Subst.compress signature_t in
                               uu____4378.FStar_Syntax_Syntax.n in
                             (match uu____4377 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4386)
                                  ->
                                  let bs1 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  let repr_t =
                                    let repr_ts =
                                      let uu____4412 = repr in
                                      match uu____4412 with
                                      | (us, t, uu____4427) -> (us, t) in
                                    let uu____4444 =
                                      FStar_TypeChecker_Env.inst_tscheme_with
                                        repr_ts
                                        [FStar_Syntax_Syntax.U_unknown] in
                                    FStar_All.pipe_right uu____4444
                                      FStar_Pervasives_Native.snd in
                                  let repr_t_applied =
                                    let uu____4458 =
                                      let uu____4459 =
                                        let uu____4476 =
                                          let uu____4487 =
                                            let uu____4490 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.map
                                                   FStar_Pervasives_Native.fst) in
                                            FStar_All.pipe_right uu____4490
                                              (FStar_List.map
                                                 FStar_Syntax_Syntax.bv_to_name) in
                                          FStar_All.pipe_right uu____4487
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.as_arg) in
                                        (repr_t, uu____4476) in
                                      FStar_Syntax_Syntax.Tm_app uu____4459 in
                                    FStar_Syntax_Syntax.mk uu____4458
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
                                  let uu____4542 =
                                    FStar_Syntax_Util.abs
                                      (FStar_List.append bs1 [f_b; g_b; b_b])
                                      repr_t_applied
                                      FStar_Pervasives_Native.None in
                                  ([], uu____4542)
                              | uu____4573 -> failwith "Impossible!"))
                    | uu____4578 -> ts in
                  let r =
                    (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                  let uu____4580 =
                    check_and_gen1 "if_then_else" Prims.int_one
                      if_then_else_ts in
                  match uu____4580 with
                  | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                      let uu____4602 =
                        FStar_Syntax_Subst.open_univ_vars if_then_else_us
                          if_then_else_t in
                      (match uu____4602 with
                       | (us, t) ->
                           let uu____4621 =
                             FStar_Syntax_Subst.open_univ_vars
                               if_then_else_us if_then_else_ty in
                           (match uu____4621 with
                            | (uu____4638, ty) ->
                                let env =
                                  FStar_TypeChecker_Env.push_univ_vars env0
                                    us in
                                (check_no_subtyping_for_layered_combinator
                                   env t (FStar_Pervasives_Native.Some ty);
                                 (let uu____4642 = fresh_a_and_u_a "a" in
                                  match uu____4642 with
                                  | (a, u_a) ->
                                      let rest_bs =
                                        let uu____4670 =
                                          let uu____4671 =
                                            FStar_Syntax_Subst.compress ty in
                                          uu____4671.FStar_Syntax_Syntax.n in
                                        match uu____4670 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu____4683) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____4710 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            (match uu____4710 with
                                             | (a', uu____4720)::bs1 ->
                                                 let uu____4740 =
                                                   let uu____4741 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (3)))) in
                                                   FStar_All.pipe_right
                                                     uu____4741
                                                     FStar_Pervasives_Native.fst in
                                                 let uu____4838 =
                                                   let uu____4851 =
                                                     let uu____4854 =
                                                       let uu____4855 =
                                                         let uu____4862 =
                                                           let uu____4865 =
                                                             FStar_All.pipe_right
                                                               a
                                                               FStar_Pervasives_Native.fst in
                                                           FStar_All.pipe_right
                                                             uu____4865
                                                             FStar_Syntax_Syntax.bv_to_name in
                                                         (a', uu____4862) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4855 in
                                                     [uu____4854] in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____4851 in
                                                 FStar_All.pipe_right
                                                   uu____4740 uu____4838)
                                        | uu____4886 ->
                                            not_an_arrow_error "if_then_else"
                                              (Prims.of_int (4)) ty r in
                                      let bs = a :: rest_bs in
                                      let uu____4902 =
                                        let uu____4913 =
                                          let uu____4918 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs in
                                          let uu____4919 =
                                            let uu____4920 =
                                              FStar_All.pipe_right a
                                                FStar_Pervasives_Native.fst in
                                            FStar_All.pipe_right uu____4920
                                              FStar_Syntax_Syntax.bv_to_name in
                                          fresh_repr r uu____4918 u_a
                                            uu____4919 in
                                        match uu____4913 with
                                        | (repr1, g) ->
                                            let uu____4941 =
                                              let uu____4948 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1 in
                                              FStar_All.pipe_right uu____4948
                                                FStar_Syntax_Syntax.mk_binder in
                                            (uu____4941, g) in
                                      (match uu____4902 with
                                       | (f_bs, guard_f) ->
                                           let uu____4987 =
                                             let uu____4998 =
                                               let uu____5003 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs in
                                               let uu____5004 =
                                                 let uu____5005 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst in
                                                 FStar_All.pipe_right
                                                   uu____5005
                                                   FStar_Syntax_Syntax.bv_to_name in
                                               fresh_repr r uu____5003 u_a
                                                 uu____5004 in
                                             match uu____4998 with
                                             | (repr1, g) ->
                                                 let uu____5026 =
                                                   let uu____5033 =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       repr1 in
                                                   FStar_All.pipe_right
                                                     uu____5033
                                                     FStar_Syntax_Syntax.mk_binder in
                                                 (uu____5026, g) in
                                           (match uu____4987 with
                                            | (g_bs, guard_g) ->
                                                let p_b =
                                                  let uu____5079 =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "p"
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.t_bool in
                                                  FStar_All.pipe_right
                                                    uu____5079
                                                    FStar_Syntax_Syntax.mk_binder in
                                                let uu____5086 =
                                                  let uu____5091 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env
                                                      (FStar_List.append bs
                                                         [p_b]) in
                                                  let uu____5110 =
                                                    let uu____5111 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst in
                                                    FStar_All.pipe_right
                                                      uu____5111
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  fresh_repr r uu____5091 u_a
                                                    uu____5110 in
                                                (match uu____5086 with
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
                                                       (let uu____5173 =
                                                          let uu____5174 =
                                                            FStar_Syntax_Subst.compress
                                                              k1 in
                                                          uu____5174.FStar_Syntax_Syntax.n in
                                                        match uu____5173 with
                                                        | FStar_Syntax_Syntax.Tm_abs
                                                            (bs1, body,
                                                             uu____5179)
                                                            ->
                                                            let uu____5204 =
                                                              FStar_Syntax_Subst.open_term
                                                                bs1 body in
                                                            (match uu____5204
                                                             with
                                                             | (a1::bs2,
                                                                body1) ->
                                                                 let uu____5232
                                                                   =
                                                                   let uu____5259
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                   FStar_All.pipe_right
                                                                    uu____5259
                                                                    (fun
                                                                    uu____5343
                                                                    ->
                                                                    match uu____5343
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5424
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5451
                                                                    =
                                                                    let uu____5458
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5458
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____5424,
                                                                    uu____5451)) in
                                                                 (match uu____5232
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
                                                       (let uu____5589 =
                                                          FStar_All.pipe_right
                                                            k1
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               if_then_else_us) in
                                                        (if_then_else_us,
                                                          uu____5589,
                                                          if_then_else_ty))))))))))) in
                log_combinator "if_then_else" if_then_else;
                (let r =
                   let uu____5603 =
                     let uu____5606 =
                       let uu____5615 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator in
                       FStar_All.pipe_right uu____5615 FStar_Util.must in
                     FStar_All.pipe_right uu____5606
                       FStar_Pervasives_Native.snd in
                   uu____5603.FStar_Syntax_Syntax.pos in
                 let binder_aq_to_arg_aq aq =
                   match aq with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5690) -> aq
                   | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                       uu____5691) ->
                       FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit false)
                   | uu____5692 -> FStar_Pervasives_Native.None in
                 let uu____5695 = if_then_else in
                 match uu____5695 with
                 | (ite_us, ite_t, uu____5710) ->
                     let uu____5723 =
                       FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                     (match uu____5723 with
                      | (us, ite_t1) ->
                          let uu____5730 =
                            let uu____5747 =
                              let uu____5748 =
                                FStar_Syntax_Subst.compress ite_t1 in
                              uu____5748.FStar_Syntax_Syntax.n in
                            match uu____5747 with
                            | FStar_Syntax_Syntax.Tm_abs
                                (bs, uu____5768, uu____5769) ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs in
                                let uu____5795 =
                                  let uu____5808 =
                                    let uu____5813 =
                                      let uu____5816 =
                                        let uu____5825 =
                                          FStar_All.pipe_right bs1
                                            (FStar_List.splitAt
                                               ((FStar_List.length bs1) -
                                                  (Prims.of_int (3)))) in
                                        FStar_All.pipe_right uu____5825
                                          FStar_Pervasives_Native.snd in
                                      FStar_All.pipe_right uu____5816
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    FStar_All.pipe_right uu____5813
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.bv_to_name) in
                                  FStar_All.pipe_right uu____5808
                                    (fun l ->
                                       let uu____5980 = l in
                                       match uu____5980 with
                                       | f::g::p::[] -> (f, g, p)) in
                                (match uu____5795 with
                                 | (f, g, p) ->
                                     let uu____6051 =
                                       let uu____6052 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env0 us in
                                       FStar_TypeChecker_Env.push_binders
                                         uu____6052 bs1 in
                                     let uu____6053 =
                                       let uu____6054 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.map
                                              (fun uu____6079 ->
                                                 match uu____6079 with
                                                 | (b, qual) ->
                                                     let uu____6098 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     (uu____6098,
                                                       (binder_aq_to_arg_aq
                                                          qual)))) in
                                       FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                         uu____6054 r in
                                     (uu____6051, uu____6053, f, g, p))
                            | uu____6107 ->
                                failwith
                                  "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                          (match uu____5730 with
                           | (env, ite_t_applied, f_t, g_t, p_t) ->
                               let uu____6141 =
                                 let uu____6150 = stronger_repr in
                                 match uu____6150 with
                                 | (uu____6171, subcomp_t, subcomp_ty) ->
                                     let uu____6186 =
                                       FStar_Syntax_Subst.open_univ_vars us
                                         subcomp_t in
                                     (match uu____6186 with
                                      | (uu____6199, subcomp_t1) ->
                                          let uu____6201 =
                                            let uu____6212 =
                                              FStar_Syntax_Subst.open_univ_vars
                                                us subcomp_ty in
                                            match uu____6212 with
                                            | (uu____6227, subcomp_ty1) ->
                                                let uu____6229 =
                                                  let uu____6230 =
                                                    FStar_Syntax_Subst.compress
                                                      subcomp_ty1 in
                                                  uu____6230.FStar_Syntax_Syntax.n in
                                                (match uu____6229 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs, uu____6244) ->
                                                     let uu____6265 =
                                                       FStar_All.pipe_right
                                                         bs
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs)
                                                               -
                                                               Prims.int_one)) in
                                                     (match uu____6265 with
                                                      | (bs_except_last,
                                                         last_b) ->
                                                          let uu____6370 =
                                                            FStar_All.pipe_right
                                                              bs_except_last
                                                              (FStar_List.map
                                                                 FStar_Pervasives_Native.snd) in
                                                          let uu____6397 =
                                                            let uu____6400 =
                                                              FStar_All.pipe_right
                                                                last_b
                                                                FStar_List.hd in
                                                            FStar_All.pipe_right
                                                              uu____6400
                                                              FStar_Pervasives_Native.snd in
                                                          (uu____6370,
                                                            uu____6397))
                                                 | uu____6443 ->
                                                     failwith
                                                       "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                          (match uu____6201 with
                                           | (aqs_except_last, last_aq) ->
                                               let uu____6476 =
                                                 let uu____6487 =
                                                   FStar_All.pipe_right
                                                     aqs_except_last
                                                     (FStar_List.map
                                                        binder_aq_to_arg_aq) in
                                                 let uu____6504 =
                                                   FStar_All.pipe_right
                                                     last_aq
                                                     binder_aq_to_arg_aq in
                                                 (uu____6487, uu____6504) in
                                               (match uu____6476 with
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
                                                    let uu____6616 = aux f_t in
                                                    let uu____6619 = aux g_t in
                                                    (uu____6616, uu____6619)))) in
                               (match uu____6141 with
                                | (subcomp_f, subcomp_g) ->
                                    let uu____6636 =
                                      let aux t =
                                        let uu____6653 =
                                          let uu____6654 =
                                            let uu____6681 =
                                              let uu____6698 =
                                                let uu____6707 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    ite_t_applied in
                                                FStar_Util.Inr uu____6707 in
                                              (uu____6698,
                                                FStar_Pervasives_Native.None) in
                                            (t, uu____6681,
                                              FStar_Pervasives_Native.None) in
                                          FStar_Syntax_Syntax.Tm_ascribed
                                            uu____6654 in
                                        FStar_Syntax_Syntax.mk uu____6653 r in
                                      let uu____6748 = aux subcomp_f in
                                      let uu____6749 = aux subcomp_g in
                                      (uu____6748, uu____6749) in
                                    (match uu____6636 with
                                     | (tm_subcomp_ascribed_f,
                                        tm_subcomp_ascribed_g) ->
                                         ((let uu____6753 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____6753
                                           then
                                             let uu____6754 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_f in
                                             let uu____6755 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_g in
                                             FStar_Util.print2
                                               "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                               uu____6754 uu____6755
                                           else ());
                                          (let env1 =
                                             let uu____6759 =
                                               let uu____6760 =
                                                 let uu____6761 =
                                                   FStar_All.pipe_right p_t
                                                     FStar_Syntax_Util.b2t in
                                                 FStar_Syntax_Util.mk_squash
                                                   FStar_Syntax_Syntax.U_zero
                                                   uu____6761 in
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 uu____6760 in
                                             FStar_TypeChecker_Env.push_bv
                                               env uu____6759 in
                                           let uu____6764 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env1 tm_subcomp_ascribed_f in
                                           match uu____6764 with
                                           | (uu____6771, uu____6772, g_f) ->
                                               FStar_TypeChecker_Rel.force_trivial_guard
                                                 env1 g_f);
                                          (let not_p =
                                             let uu____6776 =
                                               let uu____6777 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.not_lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_All.pipe_right
                                                 uu____6777
                                                 FStar_Syntax_Syntax.fv_to_tm in
                                             let uu____6778 =
                                               let uu____6779 =
                                                 let uu____6788 =
                                                   FStar_All.pipe_right p_t
                                                     FStar_Syntax_Util.b2t in
                                                 FStar_All.pipe_right
                                                   uu____6788
                                                   FStar_Syntax_Syntax.as_arg in
                                               [uu____6779] in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____6776 uu____6778 r in
                                           let env1 =
                                             let uu____6816 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 not_p in
                                             FStar_TypeChecker_Env.push_bv
                                               env uu____6816 in
                                           let uu____6817 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env1 tm_subcomp_ascribed_g in
                                           match uu____6817 with
                                           | (uu____6824, uu____6825, g_g) ->
                                               FStar_TypeChecker_Rel.force_trivial_guard
                                                 env1 g_g)))))));
                (let tc_action env act =
                   let env01 = env in
                   let r =
                     (act.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                   if
                     (FStar_List.length act.FStar_Syntax_Syntax.action_params)
                       <> Prims.int_zero
                   then
                     (let uu____6847 =
                        let uu____6852 =
                          let uu____6853 =
                            FStar_Ident.string_of_lid
                              ed.FStar_Syntax_Syntax.mname in
                          let uu____6854 =
                            FStar_Ident.string_of_lid
                              act.FStar_Syntax_Syntax.action_name in
                          let uu____6855 =
                            FStar_Syntax_Print.binders_to_string "; "
                              act.FStar_Syntax_Syntax.action_params in
                          FStar_Util.format3
                            "Action %s:%s has non-empty action params (%s)"
                            uu____6853 uu____6854 uu____6855 in
                        (FStar_Errors.Fatal_MalformedActionDeclaration,
                          uu____6852) in
                      FStar_Errors.raise_error uu____6847 r)
                   else ();
                   (let uu____6857 =
                      let uu____6862 =
                        FStar_Syntax_Subst.univ_var_opening
                          act.FStar_Syntax_Syntax.action_univs in
                      match uu____6862 with
                      | (usubst, us) ->
                          let uu____6885 =
                            FStar_TypeChecker_Env.push_univ_vars env us in
                          let uu____6886 =
                            let uu___651_6887 = act in
                            let uu____6888 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_defn in
                            let uu____6889 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_typ in
                            {
                              FStar_Syntax_Syntax.action_name =
                                (uu___651_6887.FStar_Syntax_Syntax.action_name);
                              FStar_Syntax_Syntax.action_unqualified_name =
                                (uu___651_6887.FStar_Syntax_Syntax.action_unqualified_name);
                              FStar_Syntax_Syntax.action_univs = us;
                              FStar_Syntax_Syntax.action_params =
                                (uu___651_6887.FStar_Syntax_Syntax.action_params);
                              FStar_Syntax_Syntax.action_defn = uu____6888;
                              FStar_Syntax_Syntax.action_typ = uu____6889
                            } in
                          (uu____6885, uu____6886) in
                    match uu____6857 with
                    | (env1, act1) ->
                        let act_typ =
                          let uu____6893 =
                            let uu____6894 =
                              FStar_Syntax_Subst.compress
                                act1.FStar_Syntax_Syntax.action_typ in
                            uu____6894.FStar_Syntax_Syntax.n in
                          match uu____6893 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                              let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                              let uu____6920 =
                                FStar_Ident.lid_equals
                                  ct.FStar_Syntax_Syntax.effect_name
                                  ed.FStar_Syntax_Syntax.mname in
                              if uu____6920
                              then
                                let repr_ts =
                                  let uu____6922 = repr in
                                  match uu____6922 with
                                  | (us, t, uu____6937) -> (us, t) in
                                let repr1 =
                                  let uu____6955 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      repr_ts
                                      ct.FStar_Syntax_Syntax.comp_univs in
                                  FStar_All.pipe_right uu____6955
                                    FStar_Pervasives_Native.snd in
                                let repr2 =
                                  let uu____6965 =
                                    let uu____6966 =
                                      FStar_Syntax_Syntax.as_arg
                                        ct.FStar_Syntax_Syntax.result_typ in
                                    uu____6966 ::
                                      (ct.FStar_Syntax_Syntax.effect_args) in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____6965 r in
                                let c1 =
                                  let uu____6984 =
                                    let uu____6987 =
                                      FStar_TypeChecker_Env.new_u_univ () in
                                    FStar_Pervasives_Native.Some uu____6987 in
                                  FStar_Syntax_Syntax.mk_Total' repr2
                                    uu____6984 in
                                FStar_Syntax_Util.arrow bs c1
                              else act1.FStar_Syntax_Syntax.action_typ
                          | uu____6989 -> act1.FStar_Syntax_Syntax.action_typ in
                        let uu____6990 =
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                            act_typ in
                        (match uu____6990 with
                         | (act_typ1, uu____6998, g_t) ->
                             let uu____7000 =
                               let uu____7007 =
                                 let uu___676_7008 =
                                   FStar_TypeChecker_Env.set_expected_typ
                                     env1 act_typ1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___676_7008.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___676_7008.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___676_7008.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___676_7008.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___676_7008.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___676_7008.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___676_7008.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___676_7008.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___676_7008.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___676_7008.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     false;
                                   FStar_TypeChecker_Env.effects =
                                     (uu___676_7008.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___676_7008.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___676_7008.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___676_7008.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___676_7008.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___676_7008.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___676_7008.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___676_7008.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___676_7008.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___676_7008.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___676_7008.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___676_7008.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___676_7008.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___676_7008.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___676_7008.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___676_7008.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___676_7008.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___676_7008.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___676_7008.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___676_7008.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___676_7008.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___676_7008.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___676_7008.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___676_7008.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___676_7008.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___676_7008.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___676_7008.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___676_7008.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___676_7008.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___676_7008.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___676_7008.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___676_7008.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___676_7008.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___676_7008.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___676_7008.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___676_7008.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 } in
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 uu____7007
                                 act1.FStar_Syntax_Syntax.action_defn in
                             (match uu____7000 with
                              | (act_defn, uu____7010, g_d) ->
                                  ((let uu____7013 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other
                                           "LayeredEffectsTc") in
                                    if uu____7013
                                    then
                                      let uu____7014 =
                                        FStar_Syntax_Print.term_to_string
                                          act_defn in
                                      let uu____7015 =
                                        FStar_Syntax_Print.term_to_string
                                          act_typ1 in
                                      FStar_Util.print2
                                        "Typechecked action definition: %s and action type: %s\n"
                                        uu____7014 uu____7015
                                    else ());
                                   (let uu____7017 =
                                      let act_typ2 =
                                        FStar_TypeChecker_Normalize.normalize
                                          [FStar_TypeChecker_Env.Beta] env1
                                          act_typ1 in
                                      let uu____7025 =
                                        let uu____7026 =
                                          FStar_Syntax_Subst.compress
                                            act_typ2 in
                                        uu____7026.FStar_Syntax_Syntax.n in
                                      match uu____7025 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____7036) ->
                                          let bs1 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          let env2 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 bs1 in
                                          let uu____7059 =
                                            FStar_Syntax_Util.type_u () in
                                          (match uu____7059 with
                                           | (t, u) ->
                                               let reason =
                                                 let uu____7073 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname in
                                                 let uu____7074 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name in
                                                 FStar_Util.format2
                                                   "implicit for return type of action %s:%s"
                                                   uu____7073 uu____7074 in
                                               let uu____7075 =
                                                 FStar_TypeChecker_Util.new_implicit_var
                                                   reason r env2 t in
                                               (match uu____7075 with
                                                | (a_tm, uu____7095, g_tm) ->
                                                    let uu____7109 =
                                                      fresh_repr r env2 u
                                                        a_tm in
                                                    (match uu____7109 with
                                                     | (repr1, g) ->
                                                         let uu____7122 =
                                                           let uu____7125 =
                                                             let uu____7128 =
                                                               let uu____7131
                                                                 =
                                                                 FStar_TypeChecker_Env.new_u_univ
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 uu____7131
                                                                 (fun
                                                                    uu____7134
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7134) in
                                                             FStar_Syntax_Syntax.mk_Total'
                                                               repr1
                                                               uu____7128 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7125 in
                                                         let uu____7135 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             g g_tm in
                                                         (uu____7122,
                                                           uu____7135))))
                                      | uu____7138 ->
                                          let uu____7139 =
                                            let uu____7144 =
                                              let uu____7145 =
                                                FStar_Ident.string_of_lid
                                                  ed.FStar_Syntax_Syntax.mname in
                                              let uu____7146 =
                                                FStar_Ident.string_of_lid
                                                  act1.FStar_Syntax_Syntax.action_name in
                                              let uu____7147 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.format3
                                                "Unexpected non-function type for action %s:%s (%s)"
                                                uu____7145 uu____7146
                                                uu____7147 in
                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                              uu____7144) in
                                          FStar_Errors.raise_error uu____7139
                                            r in
                                    match uu____7017 with
                                    | (k, g_k) ->
                                        ((let uu____7161 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____7161
                                          then
                                            let uu____7162 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print1
                                              "Expected action type: %s\n"
                                              uu____7162
                                          else ());
                                         (let g =
                                            FStar_TypeChecker_Rel.teq env1
                                              act_typ1 k in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env1) [g_t; g_d; g_k; g];
                                          (let uu____7167 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____7167
                                           then
                                             let uu____7168 =
                                               FStar_Syntax_Print.term_to_string
                                                 k in
                                             FStar_Util.print1
                                               "Expected action type after unification: %s\n"
                                               uu____7168
                                           else ());
                                          (let act_typ2 =
                                             let err_msg t =
                                               let uu____7177 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____7178 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               let uu____7179 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t in
                                               FStar_Util.format3
                                                 "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                 uu____7177 uu____7178
                                                 uu____7179 in
                                             let repr_args t =
                                               let uu____7198 =
                                                 let uu____7199 =
                                                   FStar_Syntax_Subst.compress
                                                     t in
                                                 uu____7199.FStar_Syntax_Syntax.n in
                                               match uu____7198 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (head, a::is) ->
                                                   let uu____7251 =
                                                     let uu____7252 =
                                                       FStar_Syntax_Subst.compress
                                                         head in
                                                     uu____7252.FStar_Syntax_Syntax.n in
                                                   (match uu____7251 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (uu____7261, us) ->
                                                        (us,
                                                          (FStar_Pervasives_Native.fst
                                                             a), is)
                                                    | uu____7271 ->
                                                        let uu____7272 =
                                                          let uu____7277 =
                                                            err_msg t in
                                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                            uu____7277) in
                                                        FStar_Errors.raise_error
                                                          uu____7272 r)
                                               | uu____7284 ->
                                                   let uu____7285 =
                                                     let uu____7290 =
                                                       err_msg t in
                                                     (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                       uu____7290) in
                                                   FStar_Errors.raise_error
                                                     uu____7285 r in
                                             let k1 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.Beta]
                                                 env1 k in
                                             let uu____7298 =
                                               let uu____7299 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____7299.FStar_Syntax_Syntax.n in
                                             match uu____7298 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs, c) ->
                                                 let uu____7324 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c in
                                                 (match uu____7324 with
                                                  | (bs1, c1) ->
                                                      let uu____7331 =
                                                        repr_args
                                                          (FStar_Syntax_Util.comp_result
                                                             c1) in
                                                      (match uu____7331 with
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
                                                           let uu____7342 =
                                                             FStar_Syntax_Syntax.mk_Comp
                                                               ct in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7342))
                                             | uu____7345 ->
                                                 let uu____7346 =
                                                   let uu____7351 =
                                                     err_msg k1 in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____7351) in
                                                 FStar_Errors.raise_error
                                                   uu____7346 r in
                                           (let uu____7353 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env1)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____7353
                                            then
                                              let uu____7354 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.print1
                                                "Action type after injecting it into the monad: %s\n"
                                                uu____7354
                                            else ());
                                           (let act2 =
                                              let uu____7357 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env1 act_defn in
                                              match uu____7357 with
                                              | (us, act_defn1) ->
                                                  if
                                                    act1.FStar_Syntax_Syntax.action_univs
                                                      = []
                                                  then
                                                    let uu___749_7370 = act1 in
                                                    let uu____7371 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        us act_typ2 in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___749_7370.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___749_7370.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = us;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___749_7370.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = act_defn1;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu____7371
                                                    }
                                                  else
                                                    (let uu____7373 =
                                                       ((FStar_List.length us)
                                                          =
                                                          (FStar_List.length
                                                             act1.FStar_Syntax_Syntax.action_univs))
                                                         &&
                                                         (FStar_List.forall2
                                                            (fun u1 ->
                                                               fun u2 ->
                                                                 let uu____7379
                                                                   =
                                                                   FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                 uu____7379 =
                                                                   Prims.int_zero)
                                                            us
                                                            act1.FStar_Syntax_Syntax.action_univs) in
                                                     if uu____7373
                                                     then
                                                       let uu___754_7380 =
                                                         act1 in
                                                       let uu____7381 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           act1.FStar_Syntax_Syntax.action_univs
                                                           act_typ2 in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___754_7380.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___754_7380.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           =
                                                           (uu___754_7380.FStar_Syntax_Syntax.action_univs);
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___754_7380.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7381
                                                       }
                                                     else
                                                       (let uu____7383 =
                                                          let uu____7388 =
                                                            let uu____7389 =
                                                              FStar_Ident.string_of_lid
                                                                ed.FStar_Syntax_Syntax.mname in
                                                            let uu____7390 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____7391 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                us in
                                                            let uu____7392 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                act1.FStar_Syntax_Syntax.action_univs in
                                                            FStar_Util.format4
                                                              "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                              uu____7389
                                                              uu____7390
                                                              uu____7391
                                                              uu____7392 in
                                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                            uu____7388) in
                                                        FStar_Errors.raise_error
                                                          uu____7383 r)) in
                                            act2))))))))) in
                 let tschemes_of uu____7414 =
                   match uu____7414 with | (us, t, ty) -> ((us, t), (us, ty)) in
                 let combinators =
                   let uu____7459 =
                     let uu____7460 = tschemes_of repr in
                     let uu____7465 = tschemes_of return_repr in
                     let uu____7470 = tschemes_of bind_repr in
                     let uu____7475 = tschemes_of stronger_repr in
                     let uu____7480 = tschemes_of if_then_else in
                     {
                       FStar_Syntax_Syntax.l_repr = uu____7460;
                       FStar_Syntax_Syntax.l_return = uu____7465;
                       FStar_Syntax_Syntax.l_bind = uu____7470;
                       FStar_Syntax_Syntax.l_subcomp = uu____7475;
                       FStar_Syntax_Syntax.l_if_then_else = uu____7480
                     } in
                   FStar_Syntax_Syntax.Layered_eff uu____7459 in
                 let uu___763_7485 = ed in
                 let uu____7486 =
                   FStar_List.map (tc_action env0)
                     ed.FStar_Syntax_Syntax.actions in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___763_7485.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___763_7485.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs =
                     (uu___763_7485.FStar_Syntax_Syntax.univs);
                   FStar_Syntax_Syntax.binders =
                     (uu___763_7485.FStar_Syntax_Syntax.binders);
                   FStar_Syntax_Syntax.signature =
                     (let uu____7493 = signature in
                      match uu____7493 with | (us, t, uu____7508) -> (us, t));
                   FStar_Syntax_Syntax.combinators = combinators;
                   FStar_Syntax_Syntax.actions = uu____7486;
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___763_7485.FStar_Syntax_Syntax.eff_attrs)
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
          (let uu____7554 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
               (FStar_Options.Other "ED") in
           if uu____7554
           then
             let uu____7555 = FStar_Syntax_Print.eff_decl_to_string false ed in
             FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____7555
           else ());
          (let uu____7557 =
             let uu____7562 =
               FStar_Syntax_Subst.univ_var_opening
                 ed.FStar_Syntax_Syntax.univs in
             match uu____7562 with
             | (ed_univs_subst, ed_univs) ->
                 let bs =
                   let uu____7586 =
                     FStar_Syntax_Subst.subst_binders ed_univs_subst
                       ed.FStar_Syntax_Syntax.binders in
                   FStar_Syntax_Subst.open_binders uu____7586 in
                 let uu____7587 =
                   let uu____7594 =
                     FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                   FStar_TypeChecker_TcTerm.tc_tparams uu____7594 bs in
                 (match uu____7587 with
                  | (bs1, uu____7600, uu____7601) ->
                      let uu____7602 =
                        let tmp_t =
                          let uu____7612 =
                            let uu____7615 =
                              FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                                (fun uu____7620 ->
                                   FStar_Pervasives_Native.Some uu____7620) in
                            FStar_Syntax_Syntax.mk_Total'
                              FStar_Syntax_Syntax.t_unit uu____7615 in
                          FStar_Syntax_Util.arrow bs1 uu____7612 in
                        let uu____7621 =
                          FStar_TypeChecker_Util.generalize_universes env0
                            tmp_t in
                        match uu____7621 with
                        | (us, tmp_t1) ->
                            let uu____7638 =
                              let uu____7639 =
                                let uu____7640 =
                                  FStar_All.pipe_right tmp_t1
                                    FStar_Syntax_Util.arrow_formals in
                                FStar_All.pipe_right uu____7640
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____7639
                                FStar_Syntax_Subst.close_binders in
                            (us, uu____7638) in
                      (match uu____7602 with
                       | (us, bs2) ->
                           (match ed_univs with
                            | [] -> (us, bs2)
                            | uu____7677 ->
                                let uu____7680 =
                                  ((FStar_List.length ed_univs) =
                                     (FStar_List.length us))
                                    &&
                                    (FStar_List.forall2
                                       (fun u1 ->
                                          fun u2 ->
                                            let uu____7686 =
                                              FStar_Syntax_Syntax.order_univ_name
                                                u1 u2 in
                                            uu____7686 = Prims.int_zero)
                                       ed_univs us) in
                                if uu____7680
                                then (us, bs2)
                                else
                                  (let uu____7692 =
                                     let uu____7697 =
                                       let uu____7698 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____7699 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length ed_univs) in
                                       let uu____7700 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length us) in
                                       FStar_Util.format3
                                         "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                         uu____7698 uu____7699 uu____7700 in
                                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                       uu____7697) in
                                   let uu____7701 =
                                     FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname in
                                   FStar_Errors.raise_error uu____7692
                                     uu____7701)))) in
           match uu____7557 with
           | (us, bs) ->
               let ed1 =
                 let uu___798_7709 = ed in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___798_7709.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___798_7709.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs = us;
                   FStar_Syntax_Syntax.binders = bs;
                   FStar_Syntax_Syntax.signature =
                     (uu___798_7709.FStar_Syntax_Syntax.signature);
                   FStar_Syntax_Syntax.combinators =
                     (uu___798_7709.FStar_Syntax_Syntax.combinators);
                   FStar_Syntax_Syntax.actions =
                     (uu___798_7709.FStar_Syntax_Syntax.actions);
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___798_7709.FStar_Syntax_Syntax.eff_attrs)
                 } in
               let uu____7710 = FStar_Syntax_Subst.univ_var_opening us in
               (match uu____7710 with
                | (ed_univs_subst, ed_univs) ->
                    let uu____7729 =
                      let uu____7734 =
                        FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                      FStar_Syntax_Subst.open_binders' uu____7734 in
                    (match uu____7729 with
                     | (ed_bs, ed_bs_subst) ->
                         let ed2 =
                           let op uu____7755 =
                             match uu____7755 with
                             | (us1, t) ->
                                 let t1 =
                                   let uu____7775 =
                                     FStar_Syntax_Subst.shift_subst
                                       ((FStar_List.length ed_bs) +
                                          (FStar_List.length us1))
                                       ed_univs_subst in
                                   FStar_Syntax_Subst.subst uu____7775 t in
                                 let uu____7784 =
                                   let uu____7785 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length us1) ed_bs_subst in
                                   FStar_Syntax_Subst.subst uu____7785 t1 in
                                 (us1, uu____7784) in
                           let uu___812_7790 = ed1 in
                           let uu____7791 =
                             op ed1.FStar_Syntax_Syntax.signature in
                           let uu____7792 =
                             FStar_Syntax_Util.apply_eff_combinators op
                               ed1.FStar_Syntax_Syntax.combinators in
                           let uu____7793 =
                             FStar_List.map
                               (fun a ->
                                  let uu___815_7801 = a in
                                  let uu____7802 =
                                    let uu____7803 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____7803 in
                                  let uu____7814 =
                                    let uu____7815 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____7815 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      (uu___815_7801.FStar_Syntax_Syntax.action_name);
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (uu___815_7801.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (uu___815_7801.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (uu___815_7801.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____7802;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____7814
                                  }) ed1.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___812_7790.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___812_7790.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs =
                               (uu___812_7790.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders =
                               (uu___812_7790.FStar_Syntax_Syntax.binders);
                             FStar_Syntax_Syntax.signature = uu____7791;
                             FStar_Syntax_Syntax.combinators = uu____7792;
                             FStar_Syntax_Syntax.actions = uu____7793;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___812_7790.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         ((let uu____7827 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____7827
                           then
                             let uu____7828 =
                               FStar_Syntax_Print.eff_decl_to_string false
                                 ed2 in
                             FStar_Util.print1
                               "After typechecking binders eff_decl: \n\t%s\n"
                               uu____7828
                           else ());
                          (let env =
                             let uu____7831 =
                               FStar_TypeChecker_Env.push_univ_vars env0
                                 ed_univs in
                             FStar_TypeChecker_Env.push_binders uu____7831
                               ed_bs in
                           let check_and_gen' comb n env_opt uu____7864 k =
                             match uu____7864 with
                             | (us1, t) ->
                                 let env1 =
                                   if FStar_Util.is_some env_opt
                                   then
                                     FStar_All.pipe_right env_opt
                                       FStar_Util.must
                                   else env in
                                 let uu____7880 =
                                   FStar_Syntax_Subst.open_univ_vars us1 t in
                                 (match uu____7880 with
                                  | (us2, t1) ->
                                      let t2 =
                                        match k with
                                        | FStar_Pervasives_Native.Some k1 ->
                                            let uu____7889 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                              uu____7889 t1 k1
                                        | FStar_Pervasives_Native.None ->
                                            let uu____7890 =
                                              let uu____7897 =
                                                FStar_TypeChecker_Env.push_univ_vars
                                                  env1 us2 in
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                uu____7897 t1 in
                                            (match uu____7890 with
                                             | (t2, uu____7899, g) ->
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env1 g;
                                                  t2)) in
                                      let uu____7902 =
                                        FStar_TypeChecker_Util.generalize_universes
                                          env1 t2 in
                                      (match uu____7902 with
                                       | (g_us, t3) ->
                                           (if (FStar_List.length g_us) <> n
                                            then
                                              (let error =
                                                 let uu____7915 =
                                                   FStar_Ident.string_of_lid
                                                     ed2.FStar_Syntax_Syntax.mname in
                                                 let uu____7916 =
                                                   FStar_Util.string_of_int n in
                                                 let uu____7917 =
                                                   let uu____7918 =
                                                     FStar_All.pipe_right
                                                       g_us FStar_List.length in
                                                   FStar_All.pipe_right
                                                     uu____7918
                                                     FStar_Util.string_of_int in
                                                 FStar_Util.format4
                                                   "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                   uu____7915 comb uu____7916
                                                   uu____7917 in
                                               FStar_Errors.raise_error
                                                 (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                   error)
                                                 t3.FStar_Syntax_Syntax.pos)
                                            else ();
                                            (match us2 with
                                             | [] -> (g_us, t3)
                                             | uu____7926 ->
                                                 let uu____7927 =
                                                   ((FStar_List.length us2) =
                                                      (FStar_List.length g_us))
                                                     &&
                                                     (FStar_List.forall2
                                                        (fun u1 ->
                                                           fun u2 ->
                                                             let uu____7933 =
                                                               FStar_Syntax_Syntax.order_univ_name
                                                                 u1 u2 in
                                                             uu____7933 =
                                                               Prims.int_zero)
                                                        us2 g_us) in
                                                 if uu____7927
                                                 then (g_us, t3)
                                                 else
                                                   (let uu____7939 =
                                                      let uu____7944 =
                                                        let uu____7945 =
                                                          FStar_Ident.string_of_lid
                                                            ed2.FStar_Syntax_Syntax.mname in
                                                        let uu____7946 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               us2) in
                                                        let uu____7947 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               g_us) in
                                                        FStar_Util.format4
                                                          "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                          uu____7945 comb
                                                          uu____7946
                                                          uu____7947 in
                                                      (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                        uu____7944) in
                                                    FStar_Errors.raise_error
                                                      uu____7939
                                                      t3.FStar_Syntax_Syntax.pos))))) in
                           let signature =
                             check_and_gen' "signature" Prims.int_one
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature
                               FStar_Pervasives_Native.None in
                           (let uu____7950 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "ED") in
                            if uu____7950
                            then
                              let uu____7951 =
                                FStar_Syntax_Print.tscheme_to_string
                                  signature in
                              FStar_Util.print1 "Typechecked signature: %s\n"
                                uu____7951
                            else ());
                           (let fresh_a_and_wp uu____7964 =
                              let fail t =
                                let uu____7977 =
                                  FStar_TypeChecker_Err.unexpected_signature_for_monad
                                    env ed2.FStar_Syntax_Syntax.mname t in
                                FStar_Errors.raise_error uu____7977
                                  (FStar_Pervasives_Native.snd
                                     ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                              let uu____7992 =
                                FStar_TypeChecker_Env.inst_tscheme signature in
                              match uu____7992 with
                              | (uu____8003, signature1) ->
                                  let uu____8005 =
                                    let uu____8006 =
                                      FStar_Syntax_Subst.compress signature1 in
                                    uu____8006.FStar_Syntax_Syntax.n in
                                  (match uu____8005 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs1, uu____8016) ->
                                       let bs2 =
                                         FStar_Syntax_Subst.open_binders bs1 in
                                       (match bs2 with
                                        | (a, uu____8045)::(wp, uu____8047)::[]
                                            ->
                                            (a,
                                              (wp.FStar_Syntax_Syntax.sort))
                                        | uu____8076 -> fail signature1)
                                   | uu____8077 -> fail signature1) in
                            let log_combinator s ts =
                              let uu____8089 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "ED") in
                              if uu____8089
                              then
                                let uu____8090 =
                                  FStar_Ident.string_of_lid
                                    ed2.FStar_Syntax_Syntax.mname in
                                let uu____8091 =
                                  FStar_Syntax_Print.tscheme_to_string ts in
                                FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                  uu____8090 s uu____8091
                              else () in
                            let ret_wp =
                              let uu____8094 = fresh_a_and_wp () in
                              match uu____8094 with
                              | (a, wp_sort) ->
                                  let k =
                                    let uu____8110 =
                                      let uu____8119 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____8126 =
                                        let uu____8135 =
                                          let uu____8142 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____8142 in
                                        [uu____8135] in
                                      uu____8119 :: uu____8126 in
                                    let uu____8161 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                    FStar_Syntax_Util.arrow uu____8110
                                      uu____8161 in
                                  let uu____8164 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_return_vc_combinator in
                                  check_and_gen' "ret_wp" Prims.int_one
                                    FStar_Pervasives_Native.None uu____8164
                                    (FStar_Pervasives_Native.Some k) in
                            log_combinator "ret_wp" ret_wp;
                            (let bind_wp =
                               let uu____8175 = fresh_a_and_wp () in
                               match uu____8175 with
                               | (a, wp_sort_a) ->
                                   let uu____8188 = fresh_a_and_wp () in
                                   (match uu____8188 with
                                    | (b, wp_sort_b) ->
                                        let wp_sort_a_b =
                                          let uu____8204 =
                                            let uu____8213 =
                                              let uu____8220 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____8220 in
                                            [uu____8213] in
                                          let uu____8233 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8204
                                            uu____8233 in
                                        let k =
                                          let uu____8239 =
                                            let uu____8248 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_range in
                                            let uu____8255 =
                                              let uu____8264 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu____8271 =
                                                let uu____8280 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b in
                                                let uu____8287 =
                                                  let uu____8296 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu____8303 =
                                                    let uu____8312 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a_b in
                                                    [uu____8312] in
                                                  uu____8296 :: uu____8303 in
                                                uu____8280 :: uu____8287 in
                                              uu____8264 :: uu____8271 in
                                            uu____8248 :: uu____8255 in
                                          let uu____8355 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8239
                                            uu____8355 in
                                        let uu____8358 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_bind_vc_combinator in
                                        check_and_gen' "bind_wp"
                                          (Prims.of_int (2))
                                          FStar_Pervasives_Native.None
                                          uu____8358
                                          (FStar_Pervasives_Native.Some k)) in
                             log_combinator "bind_wp" bind_wp;
                             (let stronger =
                                let uu____8369 = fresh_a_and_wp () in
                                match uu____8369 with
                                | (a, wp_sort_a) ->
                                    let uu____8382 =
                                      FStar_Syntax_Util.type_u () in
                                    (match uu____8382 with
                                     | (t, uu____8388) ->
                                         let k =
                                           let uu____8392 =
                                             let uu____8401 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a in
                                             let uu____8408 =
                                               let uu____8417 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               let uu____8424 =
                                                 let uu____8433 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____8433] in
                                               uu____8417 :: uu____8424 in
                                             uu____8401 :: uu____8408 in
                                           let uu____8464 =
                                             FStar_Syntax_Syntax.mk_Total t in
                                           FStar_Syntax_Util.arrow uu____8392
                                             uu____8464 in
                                         let uu____8467 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_stronger_vc_combinator in
                                         check_and_gen' "stronger"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           uu____8467
                                           (FStar_Pervasives_Native.Some k)) in
                              log_combinator "stronger" stronger;
                              (let if_then_else =
                                 let uu____8478 = fresh_a_and_wp () in
                                 match uu____8478 with
                                 | (a, wp_sort_a) ->
                                     let p =
                                       let uu____8492 =
                                         let uu____8495 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____8495 in
                                       let uu____8496 =
                                         let uu____8497 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____8497
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____8492
                                         uu____8496 in
                                     let k =
                                       let uu____8509 =
                                         let uu____8518 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____8525 =
                                           let uu____8534 =
                                             FStar_Syntax_Syntax.mk_binder p in
                                           let uu____8541 =
                                             let uu____8550 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____8557 =
                                               let uu____8566 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____8566] in
                                             uu____8550 :: uu____8557 in
                                           uu____8534 :: uu____8541 in
                                         uu____8518 :: uu____8525 in
                                       let uu____8603 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____8509
                                         uu____8603 in
                                     let uu____8606 =
                                       let uu____8611 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                       FStar_All.pipe_right uu____8611
                                         FStar_Util.must in
                                     check_and_gen' "if_then_else"
                                       Prims.int_one
                                       FStar_Pervasives_Native.None
                                       uu____8606
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "if_then_else" if_then_else;
                               (let ite_wp =
                                  let uu____8640 = fresh_a_and_wp () in
                                  match uu____8640 with
                                  | (a, wp_sort_a) ->
                                      let k =
                                        let uu____8656 =
                                          let uu____8665 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____8672 =
                                            let uu____8681 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a in
                                            [uu____8681] in
                                          uu____8665 :: uu____8672 in
                                        let uu____8706 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_a in
                                        FStar_Syntax_Util.arrow uu____8656
                                          uu____8706 in
                                      let uu____8709 =
                                        let uu____8714 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_wp_ite_combinator in
                                        FStar_All.pipe_right uu____8714
                                          FStar_Util.must in
                                      check_and_gen' "ite_wp" Prims.int_one
                                        FStar_Pervasives_Native.None
                                        uu____8709
                                        (FStar_Pervasives_Native.Some k) in
                                log_combinator "ite_wp" ite_wp;
                                (let close_wp =
                                   let uu____8727 = fresh_a_and_wp () in
                                   match uu____8727 with
                                   | (a, wp_sort_a) ->
                                       let b =
                                         let uu____8741 =
                                           let uu____8744 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname in
                                           FStar_Pervasives_Native.Some
                                             uu____8744 in
                                         let uu____8745 =
                                           let uu____8746 =
                                             FStar_Syntax_Util.type_u () in
                                           FStar_All.pipe_right uu____8746
                                             FStar_Pervasives_Native.fst in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____8741 uu____8745 in
                                       let wp_sort_b_a =
                                         let uu____8758 =
                                           let uu____8767 =
                                             let uu____8774 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 b in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____8774 in
                                           [uu____8767] in
                                         let uu____8787 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____8758
                                           uu____8787 in
                                       let k =
                                         let uu____8793 =
                                           let uu____8802 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____8809 =
                                             let uu____8818 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____8825 =
                                               let uu____8834 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_b_a in
                                               [uu____8834] in
                                             uu____8818 :: uu____8825 in
                                           uu____8802 :: uu____8809 in
                                         let uu____8865 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____8793
                                           uu____8865 in
                                       let uu____8868 =
                                         let uu____8873 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_wp_close_combinator in
                                         FStar_All.pipe_right uu____8873
                                           FStar_Util.must in
                                       check_and_gen' "close_wp"
                                         (Prims.of_int (2))
                                         FStar_Pervasives_Native.None
                                         uu____8868
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "close_wp" close_wp;
                                 (let trivial =
                                    let uu____8886 = fresh_a_and_wp () in
                                    match uu____8886 with
                                    | (a, wp_sort_a) ->
                                        let uu____8899 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____8899 with
                                         | (t, uu____8905) ->
                                             let k =
                                               let uu____8909 =
                                                 let uu____8918 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a in
                                                 let uu____8925 =
                                                   let uu____8934 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a in
                                                   [uu____8934] in
                                                 uu____8918 :: uu____8925 in
                                               let uu____8959 =
                                                 FStar_Syntax_Syntax.mk_GTotal
                                                   t in
                                               FStar_Syntax_Util.arrow
                                                 uu____8909 uu____8959 in
                                             let trivial =
                                               let uu____8963 =
                                                 let uu____8968 =
                                                   FStar_All.pipe_right ed2
                                                     FStar_Syntax_Util.get_wp_trivial_combinator in
                                                 FStar_All.pipe_right
                                                   uu____8968 FStar_Util.must in
                                               check_and_gen' "trivial"
                                                 Prims.int_one
                                                 FStar_Pervasives_Native.None
                                                 uu____8963
                                                 (FStar_Pervasives_Native.Some
                                                    k) in
                                             (log_combinator "trivial"
                                                trivial;
                                              trivial)) in
                                  let uu____8980 =
                                    let uu____8997 =
                                      FStar_All.pipe_right ed2
                                        FStar_Syntax_Util.get_eff_repr in
                                    match uu____8997 with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          (ed2.FStar_Syntax_Syntax.actions))
                                    | uu____9026 ->
                                        let repr =
                                          let uu____9030 = fresh_a_and_wp () in
                                          match uu____9030 with
                                          | (a, wp_sort_a) ->
                                              let uu____9043 =
                                                FStar_Syntax_Util.type_u () in
                                              (match uu____9043 with
                                               | (t, uu____9049) ->
                                                   let k =
                                                     let uu____9053 =
                                                       let uu____9062 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a in
                                                       let uu____9069 =
                                                         let uu____9078 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             wp_sort_a in
                                                         [uu____9078] in
                                                       uu____9062 ::
                                                         uu____9069 in
                                                     let uu____9103 =
                                                       FStar_Syntax_Syntax.mk_GTotal
                                                         t in
                                                     FStar_Syntax_Util.arrow
                                                       uu____9053 uu____9103 in
                                                   let uu____9106 =
                                                     let uu____9111 =
                                                       FStar_All.pipe_right
                                                         ed2
                                                         FStar_Syntax_Util.get_eff_repr in
                                                     FStar_All.pipe_right
                                                       uu____9111
                                                       FStar_Util.must in
                                                   check_and_gen' "repr"
                                                     Prims.int_one
                                                     FStar_Pervasives_Native.None
                                                     uu____9106
                                                     (FStar_Pervasives_Native.Some
                                                        k)) in
                                        (log_combinator "repr" repr;
                                         (let mk_repr' t wp =
                                            let uu____9152 =
                                              FStar_TypeChecker_Env.inst_tscheme
                                                repr in
                                            match uu____9152 with
                                            | (uu____9159, repr1) ->
                                                let repr2 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.EraseUniverses;
                                                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                    env repr1 in
                                                let uu____9162 =
                                                  let uu____9163 =
                                                    let uu____9180 =
                                                      let uu____9191 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9208 =
                                                        let uu____9219 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9219] in
                                                      uu____9191 ::
                                                        uu____9208 in
                                                    (repr2, uu____9180) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9163 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9162
                                                  FStar_Range.dummyRange in
                                          let mk_repr a wp =
                                            let uu____9285 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            mk_repr' uu____9285 wp in
                                          let destruct_repr t =
                                            let uu____9300 =
                                              let uu____9301 =
                                                FStar_Syntax_Subst.compress t in
                                              uu____9301.FStar_Syntax_Syntax.n in
                                            match uu____9300 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____9312,
                                                 (t1, uu____9314)::(wp,
                                                                    uu____9316)::[])
                                                -> (t1, wp)
                                            | uu____9375 ->
                                                failwith
                                                  "Unexpected repr type" in
                                          let return_repr =
                                            let return_repr_ts =
                                              let uu____9390 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_return_repr in
                                              FStar_All.pipe_right uu____9390
                                                FStar_Util.must in
                                            let uu____9417 =
                                              fresh_a_and_wp () in
                                            match uu____9417 with
                                            | (a, uu____9425) ->
                                                let x_a =
                                                  let uu____9431 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____9431 in
                                                let res =
                                                  let wp =
                                                    let uu____9436 =
                                                      let uu____9437 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp in
                                                      FStar_All.pipe_right
                                                        uu____9437
                                                        FStar_Pervasives_Native.snd in
                                                    let uu____9446 =
                                                      let uu____9447 =
                                                        let uu____9456 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_All.pipe_right
                                                          uu____9456
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9465 =
                                                        let uu____9476 =
                                                          let uu____9485 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____9485
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9476] in
                                                      uu____9447 ::
                                                        uu____9465 in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____9436 uu____9446
                                                      FStar_Range.dummyRange in
                                                  mk_repr a wp in
                                                let k =
                                                  let uu____9521 =
                                                    let uu____9530 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a in
                                                    let uu____9537 =
                                                      let uu____9546 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          x_a in
                                                      [uu____9546] in
                                                    uu____9530 :: uu____9537 in
                                                  let uu____9571 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res in
                                                  FStar_Syntax_Util.arrow
                                                    uu____9521 uu____9571 in
                                                let uu____9574 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env k in
                                                (match uu____9574 with
                                                 | (k1, uu____9582,
                                                    uu____9583) ->
                                                     let env1 =
                                                       let uu____9587 =
                                                         FStar_TypeChecker_Env.set_range
                                                           env
                                                           (FStar_Pervasives_Native.snd
                                                              return_repr_ts).FStar_Syntax_Syntax.pos in
                                                       FStar_Pervasives_Native.Some
                                                         uu____9587 in
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
                                               let uu____9597 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_bind_repr in
                                               FStar_All.pipe_right
                                                 uu____9597 FStar_Util.must in
                                             let r =
                                               let uu____9635 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_0
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_All.pipe_right
                                                 uu____9635
                                                 FStar_Syntax_Syntax.fv_to_tm in
                                             let uu____9636 =
                                               fresh_a_and_wp () in
                                             match uu____9636 with
                                             | (a, wp_sort_a) ->
                                                 let uu____9649 =
                                                   fresh_a_and_wp () in
                                                 (match uu____9649 with
                                                  | (b, wp_sort_b) ->
                                                      let wp_sort_a_b =
                                                        let uu____9665 =
                                                          let uu____9674 =
                                                            let uu____9681 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____9681 in
                                                          [uu____9674] in
                                                        let uu____9694 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            wp_sort_b in
                                                        FStar_Syntax_Util.arrow
                                                          uu____9665
                                                          uu____9694 in
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
                                                        let uu____9700 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "x_a"
                                                          FStar_Pervasives_Native.None
                                                          uu____9700 in
                                                      let wp_g_x =
                                                        let uu____9702 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g in
                                                        let uu____9703 =
                                                          let uu____9704 =
                                                            let uu____9713 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a in
                                                            FStar_All.pipe_right
                                                              uu____9713
                                                              FStar_Syntax_Syntax.as_arg in
                                                          [uu____9704] in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____9702
                                                          uu____9703
                                                          FStar_Range.dummyRange in
                                                      let res =
                                                        let wp =
                                                          let uu____9742 =
                                                            let uu____9743 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp in
                                                            FStar_All.pipe_right
                                                              uu____9743
                                                              FStar_Pervasives_Native.snd in
                                                          let uu____9752 =
                                                            let uu____9753 =
                                                              let uu____9756
                                                                =
                                                                let uu____9759
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                let uu____9760
                                                                  =
                                                                  let uu____9763
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                  let uu____9764
                                                                    =
                                                                    let uu____9767
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu____9768
                                                                    =
                                                                    let uu____9771
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____9771] in
                                                                    uu____9767
                                                                    ::
                                                                    uu____9768 in
                                                                  uu____9763
                                                                    ::
                                                                    uu____9764 in
                                                                uu____9759 ::
                                                                  uu____9760 in
                                                              r :: uu____9756 in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9753 in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____9742
                                                            uu____9752
                                                            FStar_Range.dummyRange in
                                                        mk_repr b wp in
                                                      let maybe_range_arg =
                                                        let uu____9789 =
                                                          FStar_Util.for_some
                                                            (FStar_Syntax_Util.attr_eq
                                                               FStar_Syntax_Util.dm4f_bind_range_attr)
                                                            ed2.FStar_Syntax_Syntax.eff_attrs in
                                                        if uu____9789
                                                        then
                                                          let uu____9798 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          let uu____9805 =
                                                            let uu____9814 =
                                                              FStar_Syntax_Syntax.null_binder
                                                                FStar_Syntax_Syntax.t_range in
                                                            [uu____9814] in
                                                          uu____9798 ::
                                                            uu____9805
                                                        else [] in
                                                      let k =
                                                        let uu____9849 =
                                                          let uu____9858 =
                                                            let uu____9867 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu____9874 =
                                                              let uu____9883
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  b in
                                                              [uu____9883] in
                                                            uu____9867 ::
                                                              uu____9874 in
                                                          let uu____9908 =
                                                            let uu____9917 =
                                                              let uu____9926
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  wp_f in
                                                              let uu____9933
                                                                =
                                                                let uu____9942
                                                                  =
                                                                  let uu____9949
                                                                    =
                                                                    let uu____9950
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu____9950 in
                                                                  FStar_Syntax_Syntax.null_binder
                                                                    uu____9949 in
                                                                let uu____9951
                                                                  =
                                                                  let uu____9960
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                  let uu____9967
                                                                    =
                                                                    let uu____9976
                                                                    =
                                                                    let uu____9983
                                                                    =
                                                                    let uu____9984
                                                                    =
                                                                    let uu____9993
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____9993] in
                                                                    let uu____10012
                                                                    =
                                                                    let uu____10015
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____10015 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____9984
                                                                    uu____10012 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____9983 in
                                                                    [uu____9976] in
                                                                  uu____9960
                                                                    ::
                                                                    uu____9967 in
                                                                uu____9942 ::
                                                                  uu____9951 in
                                                              uu____9926 ::
                                                                uu____9933 in
                                                            FStar_List.append
                                                              maybe_range_arg
                                                              uu____9917 in
                                                          FStar_List.append
                                                            uu____9858
                                                            uu____9908 in
                                                        let uu____10060 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            res in
                                                        FStar_Syntax_Util.arrow
                                                          uu____9849
                                                          uu____10060 in
                                                      let uu____10063 =
                                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                          env k in
                                                      (match uu____10063 with
                                                       | (k1, uu____10071,
                                                          uu____10072) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.set_range
                                                               env
                                                               (FStar_Pervasives_Native.snd
                                                                  bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                           let env2 =
                                                             FStar_All.pipe_right
                                                               (let uu___1010_10082
                                                                  = env1 in
                                                                {
                                                                  FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.solver);
                                                                  FStar_TypeChecker_Env.range
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.range);
                                                                  FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.curmodule);
                                                                  FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.gamma);
                                                                  FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.gamma_sig);
                                                                  FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.gamma_cache);
                                                                  FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.modules);
                                                                  FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.expected_typ);
                                                                  FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.sigtab);
                                                                  FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.attrtab);
                                                                  FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.instantiate_imp);
                                                                  FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.effects);
                                                                  FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.generalize);
                                                                  FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.letrecs);
                                                                  FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.top_level);
                                                                  FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.check_uvars);
                                                                  FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.use_eq);
                                                                  FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.use_eq_strict);
                                                                  FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.is_iface);
                                                                  FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.admit);
                                                                  FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                  FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.lax_universes);
                                                                  FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.phase1);
                                                                  FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.failhard);
                                                                  FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.nosynth);
                                                                  FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.uvar_subtyping);
                                                                  FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.tc_term);
                                                                  FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.type_of);
                                                                  FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.universe_of);
                                                                  FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.check_type_of);
                                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.use_bv_sorts);
                                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                  FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.normalized_eff_names);
                                                                  FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.fv_delta_depths);
                                                                  FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.proof_ns);
                                                                  FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.synth_hook);
                                                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                  FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.splice);
                                                                  FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.mpreprocess);
                                                                  FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.postprocess);
                                                                  FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.identifier_info);
                                                                  FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.tc_hooks);
                                                                  FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.dsenv);
                                                                  FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.nbe);
                                                                  FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.strict_args_tab);
                                                                  FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.erasable_types_tab);
                                                                  FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (
                                                                    uu___1010_10082.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                })
                                                               (fun
                                                                  uu____10083
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____10083) in
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
                                                (let uu____10102 =
                                                   if
                                                     act.FStar_Syntax_Syntax.action_univs
                                                       = []
                                                   then (env, act)
                                                   else
                                                     (let uu____10114 =
                                                        FStar_Syntax_Subst.univ_var_opening
                                                          act.FStar_Syntax_Syntax.action_univs in
                                                      match uu____10114 with
                                                      | (usubst, uvs) ->
                                                          let uu____10137 =
                                                            FStar_TypeChecker_Env.push_univ_vars
                                                              env uvs in
                                                          let uu____10138 =
                                                            let uu___1023_10139
                                                              = act in
                                                            let uu____10140 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_defn in
                                                            let uu____10141 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_typ in
                                                            {
                                                              FStar_Syntax_Syntax.action_name
                                                                =
                                                                (uu___1023_10139.FStar_Syntax_Syntax.action_name);
                                                              FStar_Syntax_Syntax.action_unqualified_name
                                                                =
                                                                (uu___1023_10139.FStar_Syntax_Syntax.action_unqualified_name);
                                                              FStar_Syntax_Syntax.action_univs
                                                                = uvs;
                                                              FStar_Syntax_Syntax.action_params
                                                                =
                                                                (uu___1023_10139.FStar_Syntax_Syntax.action_params);
                                                              FStar_Syntax_Syntax.action_defn
                                                                = uu____10140;
                                                              FStar_Syntax_Syntax.action_typ
                                                                = uu____10141
                                                            } in
                                                          (uu____10137,
                                                            uu____10138)) in
                                                 match uu____10102 with
                                                 | (env1, act1) ->
                                                     let act_typ =
                                                       let uu____10145 =
                                                         let uu____10146 =
                                                           FStar_Syntax_Subst.compress
                                                             act1.FStar_Syntax_Syntax.action_typ in
                                                         uu____10146.FStar_Syntax_Syntax.n in
                                                       match uu____10145 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let c1 =
                                                             FStar_Syntax_Util.comp_to_comp_typ
                                                               c in
                                                           let uu____10172 =
                                                             FStar_Ident.lid_equals
                                                               c1.FStar_Syntax_Syntax.effect_name
                                                               ed2.FStar_Syntax_Syntax.mname in
                                                           if uu____10172
                                                           then
                                                             let uu____10173
                                                               =
                                                               let uu____10176
                                                                 =
                                                                 let uu____10177
                                                                   =
                                                                   let uu____10178
                                                                    =
                                                                    FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                   FStar_Pervasives_Native.fst
                                                                    uu____10178 in
                                                                 mk_repr'
                                                                   c1.FStar_Syntax_Syntax.result_typ
                                                                   uu____10177 in
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 uu____10176 in
                                                             FStar_Syntax_Util.arrow
                                                               bs1
                                                               uu____10173
                                                           else
                                                             act1.FStar_Syntax_Syntax.action_typ
                                                       | uu____10200 ->
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                     let uu____10201 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env1 act_typ in
                                                     (match uu____10201 with
                                                      | (act_typ1,
                                                         uu____10209, g_t) ->
                                                          let env' =
                                                            let uu___1040_10212
                                                              =
                                                              FStar_TypeChecker_Env.set_expected_typ
                                                                env1 act_typ1 in
                                                            {
                                                              FStar_TypeChecker_Env.solver
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.solver);
                                                              FStar_TypeChecker_Env.range
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.range);
                                                              FStar_TypeChecker_Env.curmodule
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.curmodule);
                                                              FStar_TypeChecker_Env.gamma
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.gamma);
                                                              FStar_TypeChecker_Env.gamma_sig
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.gamma_sig);
                                                              FStar_TypeChecker_Env.gamma_cache
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.gamma_cache);
                                                              FStar_TypeChecker_Env.modules
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.modules);
                                                              FStar_TypeChecker_Env.expected_typ
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.expected_typ);
                                                              FStar_TypeChecker_Env.sigtab
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.sigtab);
                                                              FStar_TypeChecker_Env.attrtab
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.attrtab);
                                                              FStar_TypeChecker_Env.instantiate_imp
                                                                = false;
                                                              FStar_TypeChecker_Env.effects
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.effects);
                                                              FStar_TypeChecker_Env.generalize
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.generalize);
                                                              FStar_TypeChecker_Env.letrecs
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.letrecs);
                                                              FStar_TypeChecker_Env.top_level
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.top_level);
                                                              FStar_TypeChecker_Env.check_uvars
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.check_uvars);
                                                              FStar_TypeChecker_Env.use_eq
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.use_eq);
                                                              FStar_TypeChecker_Env.use_eq_strict
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.use_eq_strict);
                                                              FStar_TypeChecker_Env.is_iface
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.is_iface);
                                                              FStar_TypeChecker_Env.admit
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.admit);
                                                              FStar_TypeChecker_Env.lax
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.lax);
                                                              FStar_TypeChecker_Env.lax_universes
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.lax_universes);
                                                              FStar_TypeChecker_Env.phase1
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.phase1);
                                                              FStar_TypeChecker_Env.failhard
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.failhard);
                                                              FStar_TypeChecker_Env.nosynth
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.nosynth);
                                                              FStar_TypeChecker_Env.uvar_subtyping
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.uvar_subtyping);
                                                              FStar_TypeChecker_Env.tc_term
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.tc_term);
                                                              FStar_TypeChecker_Env.type_of
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.type_of);
                                                              FStar_TypeChecker_Env.universe_of
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.universe_of);
                                                              FStar_TypeChecker_Env.check_type_of
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.check_type_of);
                                                              FStar_TypeChecker_Env.use_bv_sorts
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.use_bv_sorts);
                                                              FStar_TypeChecker_Env.qtbl_name_and_index
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                              FStar_TypeChecker_Env.normalized_eff_names
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.normalized_eff_names);
                                                              FStar_TypeChecker_Env.fv_delta_depths
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.fv_delta_depths);
                                                              FStar_TypeChecker_Env.proof_ns
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.proof_ns);
                                                              FStar_TypeChecker_Env.synth_hook
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.synth_hook);
                                                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                              FStar_TypeChecker_Env.splice
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.splice);
                                                              FStar_TypeChecker_Env.mpreprocess
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.mpreprocess);
                                                              FStar_TypeChecker_Env.postprocess
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.postprocess);
                                                              FStar_TypeChecker_Env.identifier_info
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.identifier_info);
                                                              FStar_TypeChecker_Env.tc_hooks
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.tc_hooks);
                                                              FStar_TypeChecker_Env.dsenv
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.dsenv);
                                                              FStar_TypeChecker_Env.nbe
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.nbe);
                                                              FStar_TypeChecker_Env.strict_args_tab
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.strict_args_tab);
                                                              FStar_TypeChecker_Env.erasable_types_tab
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.erasable_types_tab);
                                                              FStar_TypeChecker_Env.enable_defer_to_tac
                                                                =
                                                                (uu___1040_10212.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                            } in
                                                          ((let uu____10214 =
                                                              FStar_TypeChecker_Env.debug
                                                                env1
                                                                (FStar_Options.Other
                                                                   "ED") in
                                                            if uu____10214
                                                            then
                                                              let uu____10215
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  act1.FStar_Syntax_Syntax.action_name in
                                                              let uu____10216
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act1.FStar_Syntax_Syntax.action_defn in
                                                              let uu____10217
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ1 in
                                                              FStar_Util.print3
                                                                "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                uu____10215
                                                                uu____10216
                                                                uu____10217
                                                            else ());
                                                           (let uu____10219 =
                                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                env'
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            match uu____10219
                                                            with
                                                            | (act_defn,
                                                               uu____10227,
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
                                                                let uu____10231
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
                                                                    let uu____10267
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10267
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10279)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10286
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10286 in
                                                                    let uu____10289
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10289
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10303,
                                                                    g) ->
                                                                    (k1, g)))
                                                                  | uu____10307
                                                                    ->
                                                                    let uu____10308
                                                                    =
                                                                    let uu____10313
                                                                    =
                                                                    let uu____10314
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10315
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10314
                                                                    uu____10315 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10313) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10308
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                (match uu____10231
                                                                 with
                                                                 | (expected_k,
                                                                    g_k) ->
                                                                    let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    ((
                                                                    let uu____10330
                                                                    =
                                                                    let uu____10331
                                                                    =
                                                                    let uu____10332
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10332 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10331 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10330);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu____10334
                                                                    =
                                                                    let uu____10335
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10335.FStar_Syntax_Syntax.n in
                                                                    match uu____10334
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10360
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10360
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10367
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10367
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10387
                                                                    =
                                                                    let uu____10388
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10388] in
                                                                    let uu____10389
                                                                    =
                                                                    let uu____10400
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10400] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10387;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10389;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10425
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10425))
                                                                    | 
                                                                    uu____10428
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10429
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10449
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10449)) in
                                                                    match uu____10429
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
                                                                    let uu___1090_10468
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1090_10468.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1090_10468.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1090_10468.FStar_Syntax_Syntax.action_params);
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
                                  match uu____8980 with
                                  | (repr, return_repr, bind_repr, actions)
                                      ->
                                      let cl ts =
                                        let ts1 =
                                          FStar_Syntax_Subst.close_tscheme
                                            ed_bs ts in
                                        let ed_univs_closing =
                                          FStar_Syntax_Subst.univ_var_closing
                                            ed_univs in
                                        let uu____10511 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length ed_bs)
                                            ed_univs_closing in
                                        FStar_Syntax_Subst.subst_tscheme
                                          uu____10511 ts1 in
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
                                            uu____10523 ->
                                            FStar_Syntax_Syntax.Primitive_eff
                                              combinators1
                                        | FStar_Syntax_Syntax.DM4F_eff
                                            uu____10524 ->
                                            FStar_Syntax_Syntax.DM4F_eff
                                              combinators1
                                        | uu____10525 ->
                                            failwith
                                              "Impossible! tc_eff_decl on a layered effect is not expected" in
                                      let ed3 =
                                        let uu___1110_10527 = ed2 in
                                        let uu____10528 = cl signature in
                                        let uu____10529 =
                                          FStar_List.map
                                            (fun a ->
                                               let uu___1113_10537 = a in
                                               let uu____10538 =
                                                 let uu____10539 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_defn)) in
                                                 FStar_All.pipe_right
                                                   uu____10539
                                                   FStar_Pervasives_Native.snd in
                                               let uu____10564 =
                                                 let uu____10565 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_typ)) in
                                                 FStar_All.pipe_right
                                                   uu____10565
                                                   FStar_Pervasives_Native.snd in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___1113_10537.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___1113_10537.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   =
                                                   (uu___1113_10537.FStar_Syntax_Syntax.action_univs);
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___1113_10537.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = uu____10538;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____10564
                                               }) actions in
                                        {
                                          FStar_Syntax_Syntax.mname =
                                            (uu___1110_10527.FStar_Syntax_Syntax.mname);
                                          FStar_Syntax_Syntax.cattributes =
                                            (uu___1110_10527.FStar_Syntax_Syntax.cattributes);
                                          FStar_Syntax_Syntax.univs =
                                            (uu___1110_10527.FStar_Syntax_Syntax.univs);
                                          FStar_Syntax_Syntax.binders =
                                            (uu___1110_10527.FStar_Syntax_Syntax.binders);
                                          FStar_Syntax_Syntax.signature =
                                            uu____10528;
                                          FStar_Syntax_Syntax.combinators =
                                            combinators2;
                                          FStar_Syntax_Syntax.actions =
                                            uu____10529;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            (uu___1110_10527.FStar_Syntax_Syntax.eff_attrs)
                                        } in
                                      ((let uu____10591 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "ED") in
                                        if uu____10591
                                        then
                                          let uu____10592 =
                                            FStar_Syntax_Print.eff_decl_to_string
                                              false ed3 in
                                          FStar_Util.print1
                                            "Typechecked effect declaration:\n\t%s\n"
                                            uu____10592
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
          let uu____10622 =
            let uu____10643 =
              FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
            if uu____10643
            then tc_layered_eff_decl
            else tc_non_layered_eff_decl in
          uu____10622 env ed quals attrs
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
        let fail uu____10693 =
          let uu____10694 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____10699 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____10694 uu____10699 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____10743)::(wp, uu____10745)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____10774 -> fail ())
        | uu____10775 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____10787 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____10787
       then
         let uu____10788 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____10788
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____10802 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____10802.FStar_Syntax_Syntax.pos in
       let uu____10811 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____10811 with
       | (us, lift, lift_ty) ->
           ((let uu____10822 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____10822
             then
               let uu____10823 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____10828 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____10823 uu____10828
             else ());
            (let uu____10834 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____10834 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____10849 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____10850 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____10851 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____10849 uu____10850 s uu____10851 in
                   let uu____10852 =
                     let uu____10859 =
                       let uu____10864 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____10864
                         (fun uu____10881 ->
                            match uu____10881 with
                            | (t, u) ->
                                let uu____10892 =
                                  let uu____10893 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____10893
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____10892, u)) in
                     match uu____10859 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____10911 =
                             let uu____10912 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____10912.FStar_Syntax_Syntax.n in
                           match uu____10911 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____10924)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____10951 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____10951 with
                                | (a', uu____10961)::bs1 ->
                                    let uu____10981 =
                                      let uu____10982 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____10982
                                        FStar_Pervasives_Native.fst in
                                    let uu____11047 =
                                      let uu____11060 =
                                        let uu____11063 =
                                          let uu____11064 =
                                            let uu____11071 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11071) in
                                          FStar_Syntax_Syntax.NT uu____11064 in
                                        [uu____11063] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11060 in
                                    FStar_All.pipe_right uu____10981
                                      uu____11047)
                           | uu____11086 ->
                               let uu____11087 =
                                 let uu____11092 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11092) in
                               FStar_Errors.raise_error uu____11087 r in
                         let uu____11101 =
                           let uu____11112 =
                             let uu____11117 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11124 =
                               let uu____11125 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11125
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11117 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11124 in
                           match uu____11112 with
                           | (f_sort, g) ->
                               let uu____11146 =
                                 let uu____11153 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11153
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11146, g) in
                         (match uu____11101 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11219 =
                                let uu____11224 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11225 =
                                  let uu____11226 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11226
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11224 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11225 in
                              (match uu____11219 with
                               | (repr, g_repr) ->
                                   let uu____11243 =
                                     let uu____11248 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11249 =
                                       let uu____11250 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11251 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11250 uu____11251 in
                                     pure_wp_uvar uu____11248 repr
                                       uu____11249 r in
                                   (match uu____11243 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11261 =
                                            let uu____11262 =
                                              let uu____11263 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11263] in
                                            let uu____11264 =
                                              let uu____11275 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11275] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11262;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11264;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11261 in
                                        let uu____11308 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11311 =
                                          let uu____11312 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11312 guard_wp in
                                        (uu____11308, uu____11311)))) in
                   match uu____10852 with
                   | (k, g_k) ->
                       ((let uu____11322 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11322
                         then
                           let uu____11323 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11323
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11329 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11329
                          then
                            let uu____11330 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11330
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          let check_non_informative_binders =
                            (FStar_TypeChecker_Env.is_reifiable_effect env
                               sub.FStar_Syntax_Syntax.target)
                              &&
                              (let uu____11335 =
                                 FStar_TypeChecker_Env.fv_with_lid_has_attr
                                   env sub.FStar_Syntax_Syntax.target
                                   FStar_Parser_Const.allow_informative_binders_attr in
                               Prims.op_Negation uu____11335) in
                          (let uu____11337 =
                             let uu____11338 = FStar_Syntax_Subst.compress k1 in
                             uu____11338.FStar_Syntax_Syntax.n in
                           match uu____11337 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11363 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11363 with
                                | (a::bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11394 =
                                      let uu____11413 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11413
                                        (fun uu____11488 ->
                                           match uu____11488 with
                                           | (l1, l2) ->
                                               let uu____11561 =
                                                 FStar_List.hd l2 in
                                               (l1, uu____11561)) in
                                    (match uu____11394 with
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
                             let uu___1223_11634 = sub in
                             let uu____11635 =
                               let uu____11638 =
                                 let uu____11639 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____11639) in
                               FStar_Pervasives_Native.Some uu____11638 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1223_11634.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1223_11634.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____11635;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____11653 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____11653
                            then
                              let uu____11654 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____11654
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
          let uu____11687 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____11687 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____11690 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____11690
        then tc_layered_lift env sub
        else
          (let uu____11692 =
             let uu____11699 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____11699 in
           match uu____11692 with
           | (a, wp_a_src) ->
               let uu____11706 =
                 let uu____11713 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____11713 in
               (match uu____11706 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____11721 =
                        let uu____11724 =
                          let uu____11725 =
                            let uu____11732 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____11732) in
                          FStar_Syntax_Syntax.NT uu____11725 in
                        [uu____11724] in
                      FStar_Syntax_Subst.subst uu____11721 wp_b_tgt in
                    let expected_k =
                      let uu____11740 =
                        let uu____11749 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____11756 =
                          let uu____11765 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____11765] in
                        uu____11749 :: uu____11756 in
                      let uu____11790 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____11740 uu____11790 in
                    let repr_type eff_name a1 wp =
                      (let uu____11812 =
                         let uu____11813 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____11813 in
                       if uu____11812
                       then
                         let uu____11814 =
                           let uu____11819 =
                             let uu____11820 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____11820 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____11819) in
                         let uu____11821 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____11814 uu____11821
                       else ());
                      (let uu____11823 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____11823 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____11855 =
                               let uu____11856 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____11856
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____11855 in
                           let uu____11863 =
                             let uu____11864 =
                               let uu____11881 =
                                 let uu____11892 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____11901 =
                                   let uu____11912 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____11912] in
                                 uu____11892 :: uu____11901 in
                               (repr, uu____11881) in
                             FStar_Syntax_Syntax.Tm_app uu____11864 in
                           let uu____11957 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____11863 uu____11957) in
                    let uu____11958 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12130 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12139 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12139 with
                              | (usubst, uvs1) ->
                                  let uu____12162 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12163 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12162, uu____12163)
                            else (env, lift_wp) in
                          (match uu____12130 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12208 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12208)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12279 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12292 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12292 with
                              | (usubst, uvs) ->
                                  let uu____12317 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12317)
                            else ([], lift) in
                          (match uu____12279 with
                           | (uvs, lift1) ->
                               ((let uu____12352 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12352
                                 then
                                   let uu____12353 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12353
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12356 =
                                   let uu____12363 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12363 lift1 in
                                 match uu____12356 with
                                 | (lift2, comp, uu____12388) ->
                                     let uu____12389 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12389 with
                                      | (uu____12418, lift_wp, lift_elab) ->
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
                                            let uu____12445 =
                                              let uu____12456 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____12456 in
                                            let uu____12473 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____12445, uu____12473)
                                          else
                                            (let uu____12501 =
                                               let uu____12512 =
                                                 let uu____12521 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____12521) in
                                               FStar_Pervasives_Native.Some
                                                 uu____12512 in
                                             let uu____12536 =
                                               let uu____12545 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____12545) in
                                             (uu____12501, uu____12536)))))) in
                    (match uu____11958 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1307_12609 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1307_12609.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1307_12609.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1307_12609.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1307_12609.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1307_12609.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1307_12609.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1307_12609.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1307_12609.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1307_12609.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1307_12609.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1307_12609.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1307_12609.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1307_12609.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1307_12609.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1307_12609.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1307_12609.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1307_12609.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1307_12609.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1307_12609.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1307_12609.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1307_12609.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1307_12609.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1307_12609.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1307_12609.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1307_12609.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1307_12609.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1307_12609.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1307_12609.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1307_12609.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1307_12609.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1307_12609.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1307_12609.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1307_12609.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1307_12609.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1307_12609.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1307_12609.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1307_12609.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1307_12609.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1307_12609.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1307_12609.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1307_12609.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1307_12609.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1307_12609.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1307_12609.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1307_12609.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1307_12609.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____12641 =
                                 let uu____12646 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____12646 with
                                 | (usubst, uvs1) ->
                                     let uu____12669 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____12670 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____12669, uu____12670) in
                               (match uu____12641 with
                                | (env2, lift2) ->
                                    let uu____12675 =
                                      let uu____12682 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____12682 in
                                    (match uu____12675 with
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
                                             let uu____12708 =
                                               let uu____12709 =
                                                 let uu____12726 =
                                                   let uu____12737 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____12746 =
                                                     let uu____12757 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____12757] in
                                                   uu____12737 :: uu____12746 in
                                                 (lift_wp1, uu____12726) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____12709 in
                                             let uu____12802 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____12708 uu____12802 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____12806 =
                                             let uu____12815 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____12822 =
                                               let uu____12831 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____12838 =
                                                 let uu____12847 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____12847] in
                                               uu____12831 :: uu____12838 in
                                             uu____12815 :: uu____12822 in
                                           let uu____12878 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____12806 uu____12878 in
                                         let uu____12881 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____12881 with
                                          | (expected_k2, uu____12891,
                                             uu____12892) ->
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
                                                   let uu____12896 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____12896)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____12904 =
                             let uu____12905 =
                               let uu____12906 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____12906
                                 FStar_List.length in
                             uu____12905 <> Prims.int_one in
                           if uu____12904
                           then
                             let uu____12925 =
                               let uu____12930 =
                                 let uu____12931 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12932 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12933 =
                                   let uu____12934 =
                                     let uu____12935 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12935
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12934
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12931 uu____12932 uu____12933 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12930) in
                             FStar_Errors.raise_error uu____12925 r
                           else ());
                          (let uu____12956 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____12958 =
                                  let uu____12959 =
                                    let uu____12962 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____12962
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____12959
                                    FStar_List.length in
                                uu____12958 <> Prims.int_one) in
                           if uu____12956
                           then
                             let uu____12997 =
                               let uu____13002 =
                                 let uu____13003 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____13004 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____13005 =
                                   let uu____13006 =
                                     let uu____13007 =
                                       let uu____13010 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____13010
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____13007
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____13006
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____13003 uu____13004 uu____13005 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____13002) in
                             FStar_Errors.raise_error uu____12997 r
                           else ());
                          (let uu___1344_13046 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1344_13046.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1344_13046.FStar_Syntax_Syntax.target);
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
    fun uu____13076 ->
      fun r ->
        match uu____13076 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13099 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13123 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13123 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13154 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13154 c in
                     let uu____13163 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13163, uvs1, tps1, c1)) in
            (match uu____13099 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13183 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13183 with
                  | (tps2, c2) ->
                      let uu____13198 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13198 with
                       | (tps3, env3, us) ->
                           let uu____13216 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13216 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13242)::uu____13243 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13262 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13268 =
                                    let uu____13269 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13269 in
                                  if uu____13268
                                  then
                                    let uu____13270 =
                                      let uu____13275 =
                                        let uu____13276 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13277 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13276 uu____13277 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13275) in
                                    FStar_Errors.raise_error uu____13270 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13281 =
                                    let uu____13282 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____13282 in
                                  match uu____13281 with
                                  | (uvs2, t) ->
                                      let uu____13311 =
                                        let uu____13316 =
                                          let uu____13329 =
                                            let uu____13330 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13330.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13329) in
                                        match uu____13316 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13345, c5)) -> ([], c5)
                                        | (uu____13387,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____13426 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13311 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____13454 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____13454 with
                                               | (uu____13459, t1) ->
                                                   let uu____13461 =
                                                     let uu____13466 =
                                                       let uu____13467 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____13468 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____13469 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____13467
                                                         uu____13468
                                                         uu____13469 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____13466) in
                                                   FStar_Errors.raise_error
                                                     uu____13461 r)
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
              let uu____13505 =
                let uu____13506 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13506 FStar_Ident.string_of_id in
              let uu____13507 =
                let uu____13508 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13508 FStar_Ident.string_of_id in
              let uu____13509 =
                let uu____13510 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13510 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____13505 uu____13507
                uu____13509 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____13516 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____13516 with
            | (us, t, ty) ->
                let uu____13530 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____13530 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____13543 =
                         let uu____13548 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____13548
                           (fun uu____13565 ->
                              match uu____13565 with
                              | (t1, u) ->
                                  let uu____13576 =
                                    let uu____13577 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____13577
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____13576, u)) in
                       match uu____13543 with
                       | (a, u_a) ->
                           let uu____13584 =
                             let uu____13589 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____13589
                               (fun uu____13606 ->
                                  match uu____13606 with
                                  | (t1, u) ->
                                      let uu____13617 =
                                        let uu____13618 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____13618
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13617, u)) in
                           (match uu____13584 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____13634 =
                                    let uu____13635 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____13635.FStar_Syntax_Syntax.n in
                                  match uu____13634 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____13647) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____13674 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____13674 with
                                       | (a', uu____13684)::(b', uu____13686)::bs1
                                           ->
                                           let uu____13716 =
                                             let uu____13717 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____13717
                                               FStar_Pervasives_Native.fst in
                                           let uu____13782 =
                                             let uu____13795 =
                                               let uu____13798 =
                                                 let uu____13799 =
                                                   let uu____13806 =
                                                     let uu____13809 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____13809
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____13806) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____13799 in
                                               let uu____13822 =
                                                 let uu____13825 =
                                                   let uu____13826 =
                                                     let uu____13833 =
                                                       let uu____13836 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____13836
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____13833) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____13826 in
                                                 [uu____13825] in
                                               uu____13798 :: uu____13822 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____13795 in
                                           FStar_All.pipe_right uu____13716
                                             uu____13782)
                                  | uu____13857 ->
                                      let uu____13858 =
                                        let uu____13863 =
                                          let uu____13864 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____13865 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____13864 uu____13865 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____13863) in
                                      FStar_Errors.raise_error uu____13858 r in
                                let bs = a :: b :: rest_bs in
                                let uu____13895 =
                                  let uu____13906 =
                                    let uu____13911 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____13912 =
                                      let uu____13913 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____13913
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____13911 r m u_a uu____13912 in
                                  match uu____13906 with
                                  | (repr, g) ->
                                      let uu____13934 =
                                        let uu____13941 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____13941
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13934, g) in
                                (match uu____13895 with
                                 | (f, guard_f) ->
                                     let uu____13972 =
                                       let x_a =
                                         let uu____13990 =
                                           let uu____13991 =
                                             let uu____13992 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____13992
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____13991 in
                                         FStar_All.pipe_right uu____13990
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____14007 =
                                         let uu____14012 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____14031 =
                                           let uu____14032 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____14032
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____14012 r n u_b uu____14031 in
                                       match uu____14007 with
                                       | (repr, g) ->
                                           let uu____14053 =
                                             let uu____14060 =
                                               let uu____14061 =
                                                 let uu____14062 =
                                                   let uu____14065 =
                                                     let uu____14068 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14068 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14065 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14062 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14061 in
                                             FStar_All.pipe_right uu____14060
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____14053, g) in
                                     (match uu____13972 with
                                      | (g, guard_g) ->
                                          let uu____14111 =
                                            let uu____14116 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14117 =
                                              let uu____14118 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14118
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14116 r p u_b uu____14117 in
                                          (match uu____14111 with
                                           | (repr, guard_repr) ->
                                               let uu____14133 =
                                                 let uu____14138 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14139 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14138
                                                   repr uu____14139 r in
                                               (match uu____14133 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14149 =
                                                        let uu____14152 =
                                                          let uu____14153 =
                                                            let uu____14154 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14154] in
                                                          let uu____14155 =
                                                            let uu____14166 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14166] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14153;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14155;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14152 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14149 in
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
                                                     (let uu____14226 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14226
                                                      then
                                                        let uu____14227 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14232 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14227
                                                          uu____14232
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
                                                          (let uu____14241 =
                                                             FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                               env1 p
                                                               FStar_Parser_Const.allow_informative_binders_attr in
                                                           Prims.op_Negation
                                                             uu____14241) in
                                                      (let uu____14243 =
                                                         let uu____14244 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14244.FStar_Syntax_Syntax.n in
                                                       match uu____14243 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14269 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14269
                                                            with
                                                            | (a1::b1::bs2,
                                                               c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14313
                                                                  =
                                                                  let uu____14340
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____14340
                                                                    (
                                                                    fun
                                                                    uu____14424
                                                                    ->
                                                                    match uu____14424
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____14505
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____14532
                                                                    =
                                                                    let uu____14539
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____14539
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____14505,
                                                                    uu____14532)) in
                                                                (match uu____14313
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____14654
                                                                    =
                                                                    let uu____14655
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____14655.FStar_Syntax_Syntax.n in
                                                                    match uu____14654
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____14660,
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
                                                      (let uu____14704 =
                                                         let uu____14709 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____14709) in
                                                       FStar_Errors.log_issue
                                                         r uu____14704);
                                                      (let uu____14710 =
                                                         let uu____14711 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____14711) in
                                                       ((us1, t),
                                                         uu____14710))))))))))))
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
            let uu____14758 =
              let uu____14759 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____14759 FStar_Ident.string_of_id in
            let uu____14760 =
              let uu____14761 =
                let uu____14762 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14762 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____14761 in
            Prims.op_Hat uu____14758 uu____14760 in
          let uu____14763 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____14763 with
          | (us, t, ty) ->
              let uu____14777 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____14777 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____14790 =
                       let uu____14795 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____14795
                         (fun uu____14812 ->
                            match uu____14812 with
                            | (t1, u) ->
                                let uu____14823 =
                                  let uu____14824 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____14824
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____14823, u)) in
                     match uu____14790 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____14840 =
                             let uu____14841 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____14841.FStar_Syntax_Syntax.n in
                           match uu____14840 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____14853)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____14880 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____14880 with
                                | (a', uu____14890)::bs1 ->
                                    let uu____14910 =
                                      let uu____14911 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____14911
                                        FStar_Pervasives_Native.fst in
                                    let uu____15008 =
                                      let uu____15021 =
                                        let uu____15024 =
                                          let uu____15025 =
                                            let uu____15032 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____15032) in
                                          FStar_Syntax_Syntax.NT uu____15025 in
                                        [uu____15024] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____15021 in
                                    FStar_All.pipe_right uu____14910
                                      uu____15008)
                           | uu____15047 ->
                               let uu____15048 =
                                 let uu____15053 =
                                   let uu____15054 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____15055 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____15054 uu____15055 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____15053) in
                               FStar_Errors.raise_error uu____15048 r in
                         let bs = a :: rest_bs in
                         let uu____15079 =
                           let uu____15090 =
                             let uu____15095 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15096 =
                               let uu____15097 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15097
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15095 r m u uu____15096 in
                           match uu____15090 with
                           | (repr, g) ->
                               let uu____15118 =
                                 let uu____15125 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15125
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15118, g) in
                         (match uu____15079 with
                          | (f, guard_f) ->
                              let uu____15156 =
                                let uu____15161 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15162 =
                                  let uu____15163 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15163
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15161 r n u uu____15162 in
                              (match uu____15156 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15178 =
                                     let uu____15183 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15184 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15183 ret_t
                                       uu____15184 r in
                                   (match uu____15178 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15192 =
                                            let uu____15193 =
                                              let uu____15194 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15194] in
                                            let uu____15195 =
                                              let uu____15206 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15206] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15193;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15195;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15192 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15261 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15261
                                          then
                                            let uu____15262 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15262
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
                                             let uu____15269 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15269
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15273 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15273
                                            then
                                              let uu____15274 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15274
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu____15282 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation
                                                   uu____15282) in
                                            (let uu____15284 =
                                               let uu____15285 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____15285.FStar_Syntax_Syntax.n in
                                             match uu____15284 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu____15310 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu____15310 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu____15341 =
                                                        let uu____15360 =
                                                          FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_All.pipe_right
                                                          uu____15360
                                                          (fun uu____15435 ->
                                                             match uu____15435
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu____15508
                                                                   =
                                                                   FStar_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu____15508)) in
                                                      (match uu____15341 with
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
                                            (let uu____15581 =
                                               let uu____15586 =
                                                 FStar_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu____15586) in
                                             FStar_Errors.log_issue r
                                               uu____15581);
                                            (let uu____15587 =
                                               let uu____15588 =
                                                 FStar_All.pipe_right k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu____15588) in
                                             ((us1, t), uu____15587))))))))))))