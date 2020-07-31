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
                            FStar_TypeChecker_Generalize.generalize_universes
                              env t2 in
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
                let uu____2030 =
                  check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
                match uu____2030 with
                | (bind_us, bind_t, bind_ty) ->
                    let uu____2052 =
                      FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                    (match uu____2052 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____2073 = fresh_a_and_u_a "a" in
                           match uu____2073 with
                           | (a, u_a) ->
                               let uu____2092 = fresh_a_and_u_a "b" in
                               (match uu____2092 with
                                | (b, u_b) ->
                                    let rest_bs =
                                      let uu____2120 =
                                        let uu____2121 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____2121.FStar_Syntax_Syntax.n in
                                      match uu____2120 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____2133) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____2160 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____2160 with
                                           | (a', uu____2170)::(b',
                                                                uu____2172)::bs1
                                               ->
                                               let uu____2202 =
                                                 let uu____2203 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (2)))) in
                                                 FStar_All.pipe_right
                                                   uu____2203
                                                   FStar_Pervasives_Native.fst in
                                               let uu____2300 =
                                                 let uu____2313 =
                                                   let uu____2316 =
                                                     let uu____2317 =
                                                       let uu____2324 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a) in
                                                       (a', uu____2324) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2317 in
                                                   let uu____2331 =
                                                     let uu____2334 =
                                                       let uu____2335 =
                                                         let uu____2342 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                b) in
                                                         (b', uu____2342) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____2335 in
                                                     [uu____2334] in
                                                   uu____2316 :: uu____2331 in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2313 in
                                               FStar_All.pipe_right
                                                 uu____2202 uu____2300)
                                      | uu____2357 ->
                                          not_an_arrow_error "bind"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: b :: rest_bs in
                                    let uu____2379 =
                                      let uu____2390 =
                                        let uu____2395 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____2396 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____2395 u_a
                                          uu____2396 in
                                      match uu____2390 with
                                      | (repr1, g) ->
                                          let uu____2411 =
                                            let uu____2418 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____2418
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____2411, g) in
                                    (match uu____2379 with
                                     | (f, guard_f) ->
                                         let uu____2457 =
                                           let x_a = fresh_x_a "x" a in
                                           let uu____2469 =
                                             let uu____2474 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env
                                                 (FStar_List.append bs [x_a]) in
                                             let uu____2493 =
                                               FStar_All.pipe_right
                                                 (FStar_Pervasives_Native.fst
                                                    b)
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____2474 u_b
                                               uu____2493 in
                                           match uu____2469 with
                                           | (repr1, g) ->
                                               let uu____2508 =
                                                 let uu____2515 =
                                                   let uu____2516 =
                                                     let uu____2517 =
                                                       let uu____2520 =
                                                         let uu____2523 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             () in
                                                         FStar_Pervasives_Native.Some
                                                           uu____2523 in
                                                       FStar_Syntax_Syntax.mk_Total'
                                                         repr1 uu____2520 in
                                                     FStar_Syntax_Util.arrow
                                                       [x_a] uu____2517 in
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     uu____2516 in
                                                 FStar_All.pipe_right
                                                   uu____2515
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____2508, g) in
                                         (match uu____2457 with
                                          | (g, guard_g) ->
                                              let uu____2574 =
                                                let uu____2579 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs in
                                                let uu____2580 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____2579 u_b
                                                  uu____2580 in
                                              (match uu____2574 with
                                               | (repr1, guard_repr) ->
                                                   let uu____2597 =
                                                     let uu____2602 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env bs in
                                                     let uu____2603 =
                                                       let uu____2604 =
                                                         FStar_Ident.string_of_lid
                                                           ed.FStar_Syntax_Syntax.mname in
                                                       FStar_Util.format1
                                                         "implicit for pure_wp in checking bind for %s"
                                                         uu____2604 in
                                                     pure_wp_uvar uu____2602
                                                       repr1 uu____2603 r in
                                                   (match uu____2597 with
                                                    | (pure_wp_uvar1,
                                                       g_pure_wp_uvar) ->
                                                        let k =
                                                          let uu____2622 =
                                                            let uu____2625 =
                                                              let uu____2626
                                                                =
                                                                let uu____2627
                                                                  =
                                                                  FStar_TypeChecker_Env.new_u_univ
                                                                    () in
                                                                [uu____2627] in
                                                              let uu____2628
                                                                =
                                                                let uu____2639
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg in
                                                                [uu____2639] in
                                                              {
                                                                FStar_Syntax_Syntax.comp_univs
                                                                  =
                                                                  uu____2626;
                                                                FStar_Syntax_Syntax.effect_name
                                                                  =
                                                                  FStar_Parser_Const.effect_PURE_lid;
                                                                FStar_Syntax_Syntax.result_typ
                                                                  = repr1;
                                                                FStar_Syntax_Syntax.effect_args
                                                                  =
                                                                  uu____2628;
                                                                FStar_Syntax_Syntax.flags
                                                                  = []
                                                              } in
                                                            FStar_Syntax_Syntax.mk_Comp
                                                              uu____2625 in
                                                          FStar_Syntax_Util.arrow
                                                            (FStar_List.append
                                                               bs [f; g])
                                                            uu____2622 in
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
                                                          (let uu____2700 =
                                                             let uu____2701 =
                                                               FStar_Syntax_Subst.compress
                                                                 k1 in
                                                             uu____2701.FStar_Syntax_Syntax.n in
                                                           match uu____2700
                                                           with
                                                           | FStar_Syntax_Syntax.Tm_arrow
                                                               (bs1, c) ->
                                                               let uu____2726
                                                                 =
                                                                 FStar_Syntax_Subst.open_comp
                                                                   bs1 c in
                                                               (match uu____2726
                                                                with
                                                                | (a1::b1::bs2,
                                                                   c1) ->
                                                                    let res_t
                                                                    =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                    let uu____2770
                                                                    =
                                                                    let uu____2797
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____2797
                                                                    (fun
                                                                    uu____2881
                                                                    ->
                                                                    match uu____2881
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____2962
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____2989
                                                                    =
                                                                    let uu____2996
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____2996
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____2962,
                                                                    uu____2989)) in
                                                                    (match uu____2770
                                                                    with
                                                                    | 
                                                                    (bs3,
                                                                    f_b, g_b)
                                                                    ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____3111
                                                                    =
                                                                    let uu____3112
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____3112.FStar_Syntax_Syntax.n in
                                                                    match uu____3111
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____3117,
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
                                                          (let uu____3160 =
                                                             FStar_All.pipe_right
                                                               k1
                                                               (FStar_Syntax_Subst.close_univ_vars
                                                                  bind_us) in
                                                           (bind_us, bind_t,
                                                             uu____3160)))))))))))) in
              log_combinator "bind_repr" bind_repr;
              (let stronger_repr =
                 let stronger_repr =
                   let ts =
                     let uu____3195 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_stronger_repr in
                     FStar_All.pipe_right uu____3195 FStar_Util.must in
                   let uu____3222 =
                     let uu____3223 =
                       let uu____3226 =
                         FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                       FStar_All.pipe_right uu____3226
                         FStar_Syntax_Subst.compress in
                     uu____3223.FStar_Syntax_Syntax.n in
                   match uu____3222 with
                   | FStar_Syntax_Syntax.Tm_unknown ->
                       let signature_ts =
                         let uu____3238 = signature in
                         match uu____3238 with
                         | (us, t, uu____3253) -> (us, t) in
                       let uu____3270 =
                         FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                           [FStar_Syntax_Syntax.U_unknown] in
                       (match uu____3270 with
                        | (uu____3279, signature_t) ->
                            let uu____3281 =
                              let uu____3282 =
                                FStar_Syntax_Subst.compress signature_t in
                              uu____3282.FStar_Syntax_Syntax.n in
                            (match uu____3281 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3290)
                                 ->
                                 let bs1 = FStar_Syntax_Subst.open_binders bs in
                                 let repr_t =
                                   let repr_ts =
                                     let uu____3316 = repr in
                                     match uu____3316 with
                                     | (us, t, uu____3331) -> (us, t) in
                                   let uu____3348 =
                                     FStar_TypeChecker_Env.inst_tscheme_with
                                       repr_ts
                                       [FStar_Syntax_Syntax.U_unknown] in
                                   FStar_All.pipe_right uu____3348
                                     FStar_Pervasives_Native.snd in
                                 let repr_t_applied =
                                   let uu____3368 =
                                     let uu____3369 =
                                       let uu____3386 =
                                         let uu____3397 =
                                           let uu____3400 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.map
                                                  FStar_Pervasives_Native.fst) in
                                           FStar_All.pipe_right uu____3400
                                             (FStar_List.map
                                                FStar_Syntax_Syntax.bv_to_name) in
                                         FStar_All.pipe_right uu____3397
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.as_arg) in
                                       (repr_t, uu____3386) in
                                     FStar_Syntax_Syntax.Tm_app uu____3369 in
                                   FStar_Syntax_Syntax.mk uu____3368
                                     FStar_Range.dummyRange in
                                 let f_b =
                                   FStar_Syntax_Syntax.null_binder
                                     repr_t_applied in
                                 let uu____3450 =
                                   let uu____3451 =
                                     let uu____3454 =
                                       FStar_All.pipe_right f_b
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____3454
                                       FStar_Syntax_Syntax.bv_to_name in
                                   FStar_Syntax_Util.abs
                                     (FStar_List.append bs1 [f_b]) uu____3451
                                     FStar_Pervasives_Native.None in
                                 ([], uu____3450)
                             | uu____3483 -> failwith "Impossible!"))
                   | uu____3488 -> ts in
                 let r =
                   (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
                 let uu____3490 =
                   check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
                 match uu____3490 with
                 | (stronger_us, stronger_t, stronger_ty) ->
                     ((let uu____3513 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env0)
                           (FStar_Options.Other "LayeredEffectsTc") in
                       if uu____3513
                       then
                         let uu____3514 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_t) in
                         let uu____3519 =
                           FStar_Syntax_Print.tscheme_to_string
                             (stronger_us, stronger_ty) in
                         FStar_Util.print2
                           "stronger combinator typechecked with term: %s and type: %s\n"
                           uu____3514 uu____3519
                       else ());
                      (let uu____3525 =
                         FStar_Syntax_Subst.open_univ_vars stronger_us
                           stronger_ty in
                       match uu____3525 with
                       | (us, ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____3546 = fresh_a_and_u_a "a" in
                             match uu____3546 with
                             | (a, u) ->
                                 let rest_bs =
                                   let uu____3574 =
                                     let uu____3575 =
                                       FStar_Syntax_Subst.compress ty in
                                     uu____3575.FStar_Syntax_Syntax.n in
                                   match uu____3574 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs, uu____3587) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____3614 =
                                         FStar_Syntax_Subst.open_binders bs in
                                       (match uu____3614 with
                                        | (a', uu____3624)::bs1 ->
                                            let uu____3644 =
                                              let uu____3645 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - Prims.int_one)) in
                                              FStar_All.pipe_right uu____3645
                                                FStar_Pervasives_Native.fst in
                                            let uu____3742 =
                                              let uu____3755 =
                                                let uu____3758 =
                                                  let uu____3759 =
                                                    let uu____3766 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           a) in
                                                    (a', uu____3766) in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____3759 in
                                                [uu____3758] in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____3755 in
                                            FStar_All.pipe_right uu____3644
                                              uu____3742)
                                   | uu____3781 ->
                                       not_an_arrow_error "stronger"
                                         (Prims.of_int (2)) ty r in
                                 let bs = a :: rest_bs in
                                 let uu____3797 =
                                   let uu____3808 =
                                     let uu____3813 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____3814 =
                                       FStar_All.pipe_right
                                         (FStar_Pervasives_Native.fst a)
                                         FStar_Syntax_Syntax.bv_to_name in
                                     fresh_repr r uu____3813 u uu____3814 in
                                   match uu____3808 with
                                   | (repr1, g) ->
                                       let uu____3829 =
                                         let uu____3836 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr1 in
                                         FStar_All.pipe_right uu____3836
                                           FStar_Syntax_Syntax.mk_binder in
                                       (uu____3829, g) in
                                 (match uu____3797 with
                                  | (f, guard_f) ->
                                      let uu____3875 =
                                        let uu____3880 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____3881 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____3880 u uu____3881 in
                                      (match uu____3875 with
                                       | (ret_t, guard_ret_t) ->
                                           let uu____3898 =
                                             let uu____3903 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____3904 =
                                               let uu____3905 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               FStar_Util.format1
                                                 "implicit for pure_wp in checking stronger for %s"
                                                 uu____3905 in
                                             pure_wp_uvar uu____3903 ret_t
                                               uu____3904 r in
                                           (match uu____3898 with
                                            | (pure_wp_uvar1, guard_wp) ->
                                                let c =
                                                  let uu____3921 =
                                                    let uu____3922 =
                                                      let uu____3923 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          () in
                                                      [uu____3923] in
                                                    let uu____3924 =
                                                      let uu____3935 =
                                                        FStar_All.pipe_right
                                                          pure_wp_uvar1
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____3935] in
                                                    {
                                                      FStar_Syntax_Syntax.comp_univs
                                                        = uu____3922;
                                                      FStar_Syntax_Syntax.effect_name
                                                        =
                                                        FStar_Parser_Const.effect_PURE_lid;
                                                      FStar_Syntax_Syntax.result_typ
                                                        = ret_t;
                                                      FStar_Syntax_Syntax.effect_args
                                                        = uu____3924;
                                                      FStar_Syntax_Syntax.flags
                                                        = []
                                                    } in
                                                  FStar_Syntax_Syntax.mk_Comp
                                                    uu____3921 in
                                                let k =
                                                  FStar_Syntax_Util.arrow
                                                    (FStar_List.append bs [f])
                                                    c in
                                                ((let uu____3990 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env)
                                                      (FStar_Options.Other
                                                         "LayeredEffectsTc") in
                                                  if uu____3990
                                                  then
                                                    let uu____3991 =
                                                      FStar_Syntax_Print.term_to_string
                                                        k in
                                                    FStar_Util.print1
                                                      "Expected type of subcomp before unification: %s\n"
                                                      uu____3991
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
                                                     let uu____3996 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     FStar_All.pipe_right
                                                       uu____3996
                                                       (FStar_TypeChecker_Normalize.normalize
                                                          [FStar_TypeChecker_Env.Beta;
                                                          FStar_TypeChecker_Env.Eager_unfolding]
                                                          env) in
                                                   (let uu____3998 =
                                                      let uu____3999 =
                                                        FStar_Syntax_Subst.compress
                                                          k1 in
                                                      uu____3999.FStar_Syntax_Syntax.n in
                                                    match uu____3998 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs1, c1) ->
                                                        let uu____4024 =
                                                          FStar_Syntax_Subst.open_comp
                                                            bs1 c1 in
                                                        (match uu____4024
                                                         with
                                                         | (a1::bs2, c2) ->
                                                             let res_t =
                                                               FStar_Syntax_Util.comp_result
                                                                 c2 in
                                                             let uu____4055 =
                                                               let uu____4074
                                                                 =
                                                                 FStar_List.splitAt
                                                                   ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                   bs2 in
                                                               FStar_All.pipe_right
                                                                 uu____4074
                                                                 (fun
                                                                    uu____4149
                                                                    ->
                                                                    match uu____4149
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____4222
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (l1,
                                                                    uu____4222)) in
                                                             (match uu____4055
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
                                                   (let uu____4294 =
                                                      FStar_All.pipe_right k1
                                                        (FStar_Syntax_Subst.close_univ_vars
                                                           stronger_us) in
                                                    (stronger_us, stronger_t,
                                                      uu____4294)))))))))))) in
               log_combinator "stronger_repr" stronger_repr;
               (let if_then_else =
                  let if_then_else_ts =
                    let ts =
                      let uu____4329 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_layered_if_then_else_combinator in
                      FStar_All.pipe_right uu____4329 FStar_Util.must in
                    let uu____4356 =
                      let uu____4357 =
                        let uu____4360 =
                          FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                        FStar_All.pipe_right uu____4360
                          FStar_Syntax_Subst.compress in
                      uu____4357.FStar_Syntax_Syntax.n in
                    match uu____4356 with
                    | FStar_Syntax_Syntax.Tm_unknown ->
                        let signature_ts =
                          let uu____4372 = signature in
                          match uu____4372 with
                          | (us, t, uu____4387) -> (us, t) in
                        let uu____4404 =
                          FStar_TypeChecker_Env.inst_tscheme_with
                            signature_ts [FStar_Syntax_Syntax.U_unknown] in
                        (match uu____4404 with
                         | (uu____4413, signature_t) ->
                             let uu____4415 =
                               let uu____4416 =
                                 FStar_Syntax_Subst.compress signature_t in
                               uu____4416.FStar_Syntax_Syntax.n in
                             (match uu____4415 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4424)
                                  ->
                                  let bs1 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  let repr_t =
                                    let repr_ts =
                                      let uu____4450 = repr in
                                      match uu____4450 with
                                      | (us, t, uu____4465) -> (us, t) in
                                    let uu____4482 =
                                      FStar_TypeChecker_Env.inst_tscheme_with
                                        repr_ts
                                        [FStar_Syntax_Syntax.U_unknown] in
                                    FStar_All.pipe_right uu____4482
                                      FStar_Pervasives_Native.snd in
                                  let repr_t_applied =
                                    let uu____4496 =
                                      let uu____4497 =
                                        let uu____4514 =
                                          let uu____4525 =
                                            let uu____4528 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.map
                                                   FStar_Pervasives_Native.fst) in
                                            FStar_All.pipe_right uu____4528
                                              (FStar_List.map
                                                 FStar_Syntax_Syntax.bv_to_name) in
                                          FStar_All.pipe_right uu____4525
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.as_arg) in
                                        (repr_t, uu____4514) in
                                      FStar_Syntax_Syntax.Tm_app uu____4497 in
                                    FStar_Syntax_Syntax.mk uu____4496
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
                                  let uu____4580 =
                                    FStar_Syntax_Util.abs
                                      (FStar_List.append bs1 [f_b; g_b; b_b])
                                      repr_t_applied
                                      FStar_Pervasives_Native.None in
                                  ([], uu____4580)
                              | uu____4611 -> failwith "Impossible!"))
                    | uu____4616 -> ts in
                  let r =
                    (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                  let uu____4618 =
                    check_and_gen1 "if_then_else" Prims.int_one
                      if_then_else_ts in
                  match uu____4618 with
                  | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                      let uu____4640 =
                        FStar_Syntax_Subst.open_univ_vars if_then_else_us
                          if_then_else_t in
                      (match uu____4640 with
                       | (us, t) ->
                           let uu____4659 =
                             FStar_Syntax_Subst.open_univ_vars
                               if_then_else_us if_then_else_ty in
                           (match uu____4659 with
                            | (uu____4676, ty) ->
                                let env =
                                  FStar_TypeChecker_Env.push_univ_vars env0
                                    us in
                                (check_no_subtyping_for_layered_combinator
                                   env t (FStar_Pervasives_Native.Some ty);
                                 (let uu____4680 = fresh_a_and_u_a "a" in
                                  match uu____4680 with
                                  | (a, u_a) ->
                                      let rest_bs =
                                        let uu____4708 =
                                          let uu____4709 =
                                            FStar_Syntax_Subst.compress ty in
                                          uu____4709.FStar_Syntax_Syntax.n in
                                        match uu____4708 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs, uu____4721) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____4748 =
                                              FStar_Syntax_Subst.open_binders
                                                bs in
                                            (match uu____4748 with
                                             | (a', uu____4758)::bs1 ->
                                                 let uu____4778 =
                                                   let uu____4779 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (3)))) in
                                                   FStar_All.pipe_right
                                                     uu____4779
                                                     FStar_Pervasives_Native.fst in
                                                 let uu____4876 =
                                                   let uu____4889 =
                                                     let uu____4892 =
                                                       let uu____4893 =
                                                         let uu____4900 =
                                                           let uu____4903 =
                                                             FStar_All.pipe_right
                                                               a
                                                               FStar_Pervasives_Native.fst in
                                                           FStar_All.pipe_right
                                                             uu____4903
                                                             FStar_Syntax_Syntax.bv_to_name in
                                                         (a', uu____4900) in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____4893 in
                                                     [uu____4892] in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____4889 in
                                                 FStar_All.pipe_right
                                                   uu____4778 uu____4876)
                                        | uu____4924 ->
                                            not_an_arrow_error "if_then_else"
                                              (Prims.of_int (4)) ty r in
                                      let bs = a :: rest_bs in
                                      let uu____4940 =
                                        let uu____4951 =
                                          let uu____4956 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs in
                                          let uu____4957 =
                                            let uu____4958 =
                                              FStar_All.pipe_right a
                                                FStar_Pervasives_Native.fst in
                                            FStar_All.pipe_right uu____4958
                                              FStar_Syntax_Syntax.bv_to_name in
                                          fresh_repr r uu____4956 u_a
                                            uu____4957 in
                                        match uu____4951 with
                                        | (repr1, g) ->
                                            let uu____4979 =
                                              let uu____4986 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1 in
                                              FStar_All.pipe_right uu____4986
                                                FStar_Syntax_Syntax.mk_binder in
                                            (uu____4979, g) in
                                      (match uu____4940 with
                                       | (f_bs, guard_f) ->
                                           let uu____5025 =
                                             let uu____5036 =
                                               let uu____5041 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs in
                                               let uu____5042 =
                                                 let uu____5043 =
                                                   FStar_All.pipe_right a
                                                     FStar_Pervasives_Native.fst in
                                                 FStar_All.pipe_right
                                                   uu____5043
                                                   FStar_Syntax_Syntax.bv_to_name in
                                               fresh_repr r uu____5041 u_a
                                                 uu____5042 in
                                             match uu____5036 with
                                             | (repr1, g) ->
                                                 let uu____5064 =
                                                   let uu____5071 =
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       repr1 in
                                                   FStar_All.pipe_right
                                                     uu____5071
                                                     FStar_Syntax_Syntax.mk_binder in
                                                 (uu____5064, g) in
                                           (match uu____5025 with
                                            | (g_bs, guard_g) ->
                                                let p_b =
                                                  let uu____5117 =
                                                    FStar_Syntax_Syntax.gen_bv
                                                      "p"
                                                      FStar_Pervasives_Native.None
                                                      FStar_Syntax_Util.t_bool in
                                                  FStar_All.pipe_right
                                                    uu____5117
                                                    FStar_Syntax_Syntax.mk_binder in
                                                let uu____5124 =
                                                  let uu____5129 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env
                                                      (FStar_List.append bs
                                                         [p_b]) in
                                                  let uu____5148 =
                                                    let uu____5149 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst in
                                                    FStar_All.pipe_right
                                                      uu____5149
                                                      FStar_Syntax_Syntax.bv_to_name in
                                                  fresh_repr r uu____5129 u_a
                                                    uu____5148 in
                                                (match uu____5124 with
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
                                                       (let uu____5211 =
                                                          let uu____5212 =
                                                            FStar_Syntax_Subst.compress
                                                              k1 in
                                                          uu____5212.FStar_Syntax_Syntax.n in
                                                        match uu____5211 with
                                                        | FStar_Syntax_Syntax.Tm_abs
                                                            (bs1, body,
                                                             uu____5217)
                                                            ->
                                                            let uu____5242 =
                                                              FStar_Syntax_Subst.open_term
                                                                bs1 body in
                                                            (match uu____5242
                                                             with
                                                             | (a1::bs2,
                                                                body1) ->
                                                                 let uu____5270
                                                                   =
                                                                   let uu____5297
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                   FStar_All.pipe_right
                                                                    uu____5297
                                                                    (fun
                                                                    uu____5381
                                                                    ->
                                                                    match uu____5381
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5462
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5489
                                                                    =
                                                                    let uu____5496
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5496
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____5462,
                                                                    uu____5489)) in
                                                                 (match uu____5270
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
                                                       (let uu____5627 =
                                                          FStar_All.pipe_right
                                                            k1
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               if_then_else_us) in
                                                        (if_then_else_us,
                                                          uu____5627,
                                                          if_then_else_ty))))))))))) in
                log_combinator "if_then_else" if_then_else;
                (let r =
                   let uu____5641 =
                     let uu____5644 =
                       let uu____5653 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator in
                       FStar_All.pipe_right uu____5653 FStar_Util.must in
                     FStar_All.pipe_right uu____5644
                       FStar_Pervasives_Native.snd in
                   uu____5641.FStar_Syntax_Syntax.pos in
                 let binder_aq_to_arg_aq aq =
                   match aq with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit uu____5728) -> aq
                   | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                       uu____5729) ->
                       FStar_Pervasives_Native.Some
                         (FStar_Syntax_Syntax.Implicit false)
                   | uu____5730 -> FStar_Pervasives_Native.None in
                 let uu____5733 = if_then_else in
                 match uu____5733 with
                 | (ite_us, ite_t, uu____5748) ->
                     let uu____5761 =
                       FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                     (match uu____5761 with
                      | (us, ite_t1) ->
                          let uu____5768 =
                            let uu____5785 =
                              let uu____5786 =
                                FStar_Syntax_Subst.compress ite_t1 in
                              uu____5786.FStar_Syntax_Syntax.n in
                            match uu____5785 with
                            | FStar_Syntax_Syntax.Tm_abs
                                (bs, uu____5806, uu____5807) ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs in
                                let uu____5833 =
                                  let uu____5846 =
                                    let uu____5851 =
                                      let uu____5854 =
                                        let uu____5863 =
                                          FStar_All.pipe_right bs1
                                            (FStar_List.splitAt
                                               ((FStar_List.length bs1) -
                                                  (Prims.of_int (3)))) in
                                        FStar_All.pipe_right uu____5863
                                          FStar_Pervasives_Native.snd in
                                      FStar_All.pipe_right uu____5854
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst) in
                                    FStar_All.pipe_right uu____5851
                                      (FStar_List.map
                                         FStar_Syntax_Syntax.bv_to_name) in
                                  FStar_All.pipe_right uu____5846
                                    (fun l ->
                                       let uu____6018 = l in
                                       match uu____6018 with
                                       | f::g::p::[] -> (f, g, p)) in
                                (match uu____5833 with
                                 | (f, g, p) ->
                                     let uu____6089 =
                                       let uu____6090 =
                                         FStar_TypeChecker_Env.push_univ_vars
                                           env0 us in
                                       FStar_TypeChecker_Env.push_binders
                                         uu____6090 bs1 in
                                     let uu____6091 =
                                       let uu____6092 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.map
                                              (fun uu____6117 ->
                                                 match uu____6117 with
                                                 | (b, qual) ->
                                                     let uu____6136 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         b in
                                                     (uu____6136,
                                                       (binder_aq_to_arg_aq
                                                          qual)))) in
                                       FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                         uu____6092 r in
                                     (uu____6089, uu____6091, f, g, p))
                            | uu____6145 ->
                                failwith
                                  "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                          (match uu____5768 with
                           | (env, ite_t_applied, f_t, g_t, p_t) ->
                               let uu____6179 =
                                 let uu____6188 = stronger_repr in
                                 match uu____6188 with
                                 | (uu____6209, subcomp_t, subcomp_ty) ->
                                     let uu____6224 =
                                       FStar_Syntax_Subst.open_univ_vars us
                                         subcomp_t in
                                     (match uu____6224 with
                                      | (uu____6237, subcomp_t1) ->
                                          let uu____6239 =
                                            let uu____6250 =
                                              FStar_Syntax_Subst.open_univ_vars
                                                us subcomp_ty in
                                            match uu____6250 with
                                            | (uu____6265, subcomp_ty1) ->
                                                let uu____6267 =
                                                  let uu____6268 =
                                                    FStar_Syntax_Subst.compress
                                                      subcomp_ty1 in
                                                  uu____6268.FStar_Syntax_Syntax.n in
                                                (match uu____6267 with
                                                 | FStar_Syntax_Syntax.Tm_arrow
                                                     (bs, uu____6282) ->
                                                     let uu____6303 =
                                                       FStar_All.pipe_right
                                                         bs
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs)
                                                               -
                                                               Prims.int_one)) in
                                                     (match uu____6303 with
                                                      | (bs_except_last,
                                                         last_b) ->
                                                          let uu____6408 =
                                                            FStar_All.pipe_right
                                                              bs_except_last
                                                              (FStar_List.map
                                                                 FStar_Pervasives_Native.snd) in
                                                          let uu____6435 =
                                                            let uu____6438 =
                                                              FStar_All.pipe_right
                                                                last_b
                                                                FStar_List.hd in
                                                            FStar_All.pipe_right
                                                              uu____6438
                                                              FStar_Pervasives_Native.snd in
                                                          (uu____6408,
                                                            uu____6435))
                                                 | uu____6481 ->
                                                     failwith
                                                       "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                          (match uu____6239 with
                                           | (aqs_except_last, last_aq) ->
                                               let uu____6514 =
                                                 let uu____6525 =
                                                   FStar_All.pipe_right
                                                     aqs_except_last
                                                     (FStar_List.map
                                                        binder_aq_to_arg_aq) in
                                                 let uu____6542 =
                                                   FStar_All.pipe_right
                                                     last_aq
                                                     binder_aq_to_arg_aq in
                                                 (uu____6525, uu____6542) in
                                               (match uu____6514 with
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
                                                    let uu____6654 = aux f_t in
                                                    let uu____6657 = aux g_t in
                                                    (uu____6654, uu____6657)))) in
                               (match uu____6179 with
                                | (subcomp_f, subcomp_g) ->
                                    let uu____6674 =
                                      let aux t =
                                        let uu____6691 =
                                          let uu____6692 =
                                            let uu____6719 =
                                              let uu____6736 =
                                                let uu____6745 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    ite_t_applied in
                                                FStar_Util.Inr uu____6745 in
                                              (uu____6736,
                                                FStar_Pervasives_Native.None) in
                                            (t, uu____6719,
                                              FStar_Pervasives_Native.None) in
                                          FStar_Syntax_Syntax.Tm_ascribed
                                            uu____6692 in
                                        FStar_Syntax_Syntax.mk uu____6691 r in
                                      let uu____6786 = aux subcomp_f in
                                      let uu____6787 = aux subcomp_g in
                                      (uu____6786, uu____6787) in
                                    (match uu____6674 with
                                     | (tm_subcomp_ascribed_f,
                                        tm_subcomp_ascribed_g) ->
                                         ((let uu____6791 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____6791
                                           then
                                             let uu____6792 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_f in
                                             let uu____6793 =
                                               FStar_Syntax_Print.term_to_string
                                                 tm_subcomp_ascribed_g in
                                             FStar_Util.print2
                                               "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                               uu____6792 uu____6793
                                           else ());
                                          (let env1 =
                                             let uu____6797 =
                                               let uu____6798 =
                                                 let uu____6799 =
                                                   FStar_All.pipe_right p_t
                                                     FStar_Syntax_Util.b2t in
                                                 FStar_Syntax_Util.mk_squash
                                                   FStar_Syntax_Syntax.U_zero
                                                   uu____6799 in
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 uu____6798 in
                                             FStar_TypeChecker_Env.push_bv
                                               env uu____6797 in
                                           let uu____6802 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env1 tm_subcomp_ascribed_f in
                                           match uu____6802 with
                                           | (uu____6809, uu____6810, g_f) ->
                                               FStar_TypeChecker_Rel.force_trivial_guard
                                                 env1 g_f);
                                          (let not_p =
                                             let uu____6814 =
                                               let uu____6815 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.not_lid
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_All.pipe_right
                                                 uu____6815
                                                 FStar_Syntax_Syntax.fv_to_tm in
                                             let uu____6816 =
                                               let uu____6817 =
                                                 let uu____6826 =
                                                   FStar_All.pipe_right p_t
                                                     FStar_Syntax_Util.b2t in
                                                 FStar_All.pipe_right
                                                   uu____6826
                                                   FStar_Syntax_Syntax.as_arg in
                                               [uu____6817] in
                                             FStar_Syntax_Syntax.mk_Tm_app
                                               uu____6814 uu____6816 r in
                                           let env1 =
                                             let uu____6854 =
                                               FStar_Syntax_Syntax.new_bv
                                                 FStar_Pervasives_Native.None
                                                 not_p in
                                             FStar_TypeChecker_Env.push_bv
                                               env uu____6854 in
                                           let uu____6855 =
                                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                               env1 tm_subcomp_ascribed_g in
                                           match uu____6855 with
                                           | (uu____6862, uu____6863, g_g) ->
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
                     (let uu____6885 =
                        let uu____6890 =
                          let uu____6891 =
                            FStar_Ident.string_of_lid
                              ed.FStar_Syntax_Syntax.mname in
                          let uu____6892 =
                            FStar_Ident.string_of_lid
                              act.FStar_Syntax_Syntax.action_name in
                          let uu____6893 =
                            FStar_Syntax_Print.binders_to_string "; "
                              act.FStar_Syntax_Syntax.action_params in
                          FStar_Util.format3
                            "Action %s:%s has non-empty action params (%s)"
                            uu____6891 uu____6892 uu____6893 in
                        (FStar_Errors.Fatal_MalformedActionDeclaration,
                          uu____6890) in
                      FStar_Errors.raise_error uu____6885 r)
                   else ();
                   (let uu____6895 =
                      let uu____6900 =
                        FStar_Syntax_Subst.univ_var_opening
                          act.FStar_Syntax_Syntax.action_univs in
                      match uu____6900 with
                      | (usubst, us) ->
                          let uu____6923 =
                            FStar_TypeChecker_Env.push_univ_vars env us in
                          let uu____6924 =
                            let uu___651_6925 = act in
                            let uu____6926 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_defn in
                            let uu____6927 =
                              FStar_Syntax_Subst.subst usubst
                                act.FStar_Syntax_Syntax.action_typ in
                            {
                              FStar_Syntax_Syntax.action_name =
                                (uu___651_6925.FStar_Syntax_Syntax.action_name);
                              FStar_Syntax_Syntax.action_unqualified_name =
                                (uu___651_6925.FStar_Syntax_Syntax.action_unqualified_name);
                              FStar_Syntax_Syntax.action_univs = us;
                              FStar_Syntax_Syntax.action_params =
                                (uu___651_6925.FStar_Syntax_Syntax.action_params);
                              FStar_Syntax_Syntax.action_defn = uu____6926;
                              FStar_Syntax_Syntax.action_typ = uu____6927
                            } in
                          (uu____6923, uu____6924) in
                    match uu____6895 with
                    | (env1, act1) ->
                        let act_typ =
                          let uu____6931 =
                            let uu____6932 =
                              FStar_Syntax_Subst.compress
                                act1.FStar_Syntax_Syntax.action_typ in
                            uu____6932.FStar_Syntax_Syntax.n in
                          match uu____6931 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                              let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                              let uu____6958 =
                                FStar_Ident.lid_equals
                                  ct.FStar_Syntax_Syntax.effect_name
                                  ed.FStar_Syntax_Syntax.mname in
                              if uu____6958
                              then
                                let repr_ts =
                                  let uu____6960 = repr in
                                  match uu____6960 with
                                  | (us, t, uu____6975) -> (us, t) in
                                let repr1 =
                                  let uu____6993 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      repr_ts
                                      ct.FStar_Syntax_Syntax.comp_univs in
                                  FStar_All.pipe_right uu____6993
                                    FStar_Pervasives_Native.snd in
                                let repr2 =
                                  let uu____7003 =
                                    let uu____7004 =
                                      FStar_Syntax_Syntax.as_arg
                                        ct.FStar_Syntax_Syntax.result_typ in
                                    uu____7004 ::
                                      (ct.FStar_Syntax_Syntax.effect_args) in
                                  FStar_Syntax_Syntax.mk_Tm_app repr1
                                    uu____7003 r in
                                let c1 =
                                  let uu____7022 =
                                    let uu____7025 =
                                      FStar_TypeChecker_Env.new_u_univ () in
                                    FStar_Pervasives_Native.Some uu____7025 in
                                  FStar_Syntax_Syntax.mk_Total' repr2
                                    uu____7022 in
                                FStar_Syntax_Util.arrow bs c1
                              else act1.FStar_Syntax_Syntax.action_typ
                          | uu____7027 -> act1.FStar_Syntax_Syntax.action_typ in
                        let uu____7028 =
                          FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                            act_typ in
                        (match uu____7028 with
                         | (act_typ1, uu____7036, g_t) ->
                             let uu____7038 =
                               let uu____7045 =
                                 let uu___676_7046 =
                                   FStar_TypeChecker_Env.set_expected_typ
                                     env1 act_typ1 in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___676_7046.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___676_7046.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___676_7046.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___676_7046.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_sig =
                                     (uu___676_7046.FStar_TypeChecker_Env.gamma_sig);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___676_7046.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___676_7046.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___676_7046.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___676_7046.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.attrtab =
                                     (uu___676_7046.FStar_TypeChecker_Env.attrtab);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     false;
                                   FStar_TypeChecker_Env.effects =
                                     (uu___676_7046.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___676_7046.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___676_7046.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___676_7046.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___676_7046.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___676_7046.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.use_eq_strict =
                                     (uu___676_7046.FStar_TypeChecker_Env.use_eq_strict);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___676_7046.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___676_7046.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax =
                                     (uu___676_7046.FStar_TypeChecker_Env.lax);
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___676_7046.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.phase1 =
                                     (uu___676_7046.FStar_TypeChecker_Env.phase1);
                                   FStar_TypeChecker_Env.failhard =
                                     (uu___676_7046.FStar_TypeChecker_Env.failhard);
                                   FStar_TypeChecker_Env.nosynth =
                                     (uu___676_7046.FStar_TypeChecker_Env.nosynth);
                                   FStar_TypeChecker_Env.uvar_subtyping =
                                     (uu___676_7046.FStar_TypeChecker_Env.uvar_subtyping);
                                   FStar_TypeChecker_Env.tc_term =
                                     (uu___676_7046.FStar_TypeChecker_Env.tc_term);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___676_7046.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___676_7046.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.check_type_of =
                                     (uu___676_7046.FStar_TypeChecker_Env.check_type_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___676_7046.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qtbl_name_and_index
                                     =
                                     (uu___676_7046.FStar_TypeChecker_Env.qtbl_name_and_index);
                                   FStar_TypeChecker_Env.normalized_eff_names
                                     =
                                     (uu___676_7046.FStar_TypeChecker_Env.normalized_eff_names);
                                   FStar_TypeChecker_Env.fv_delta_depths =
                                     (uu___676_7046.FStar_TypeChecker_Env.fv_delta_depths);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___676_7046.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth_hook =
                                     (uu___676_7046.FStar_TypeChecker_Env.synth_hook);
                                   FStar_TypeChecker_Env.try_solve_implicits_hook
                                     =
                                     (uu___676_7046.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                   FStar_TypeChecker_Env.splice =
                                     (uu___676_7046.FStar_TypeChecker_Env.splice);
                                   FStar_TypeChecker_Env.mpreprocess =
                                     (uu___676_7046.FStar_TypeChecker_Env.mpreprocess);
                                   FStar_TypeChecker_Env.postprocess =
                                     (uu___676_7046.FStar_TypeChecker_Env.postprocess);
                                   FStar_TypeChecker_Env.identifier_info =
                                     (uu___676_7046.FStar_TypeChecker_Env.identifier_info);
                                   FStar_TypeChecker_Env.tc_hooks =
                                     (uu___676_7046.FStar_TypeChecker_Env.tc_hooks);
                                   FStar_TypeChecker_Env.dsenv =
                                     (uu___676_7046.FStar_TypeChecker_Env.dsenv);
                                   FStar_TypeChecker_Env.nbe =
                                     (uu___676_7046.FStar_TypeChecker_Env.nbe);
                                   FStar_TypeChecker_Env.strict_args_tab =
                                     (uu___676_7046.FStar_TypeChecker_Env.strict_args_tab);
                                   FStar_TypeChecker_Env.erasable_types_tab =
                                     (uu___676_7046.FStar_TypeChecker_Env.erasable_types_tab);
                                   FStar_TypeChecker_Env.enable_defer_to_tac
                                     =
                                     (uu___676_7046.FStar_TypeChecker_Env.enable_defer_to_tac)
                                 } in
                               FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                 uu____7045
                                 act1.FStar_Syntax_Syntax.action_defn in
                             (match uu____7038 with
                              | (act_defn, uu____7048, g_d) ->
                                  ((let uu____7051 =
                                      FStar_All.pipe_left
                                        (FStar_TypeChecker_Env.debug env1)
                                        (FStar_Options.Other
                                           "LayeredEffectsTc") in
                                    if uu____7051
                                    then
                                      let uu____7052 =
                                        FStar_Syntax_Print.term_to_string
                                          act_defn in
                                      let uu____7053 =
                                        FStar_Syntax_Print.term_to_string
                                          act_typ1 in
                                      FStar_Util.print2
                                        "Typechecked action definition: %s and action type: %s\n"
                                        uu____7052 uu____7053
                                    else ());
                                   (let uu____7055 =
                                      let act_typ2 =
                                        FStar_TypeChecker_Normalize.normalize
                                          [FStar_TypeChecker_Env.Beta] env1
                                          act_typ1 in
                                      let uu____7063 =
                                        let uu____7064 =
                                          FStar_Syntax_Subst.compress
                                            act_typ2 in
                                        uu____7064.FStar_Syntax_Syntax.n in
                                      match uu____7063 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____7074) ->
                                          let bs1 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          let env2 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1 bs1 in
                                          let uu____7097 =
                                            FStar_Syntax_Util.type_u () in
                                          (match uu____7097 with
                                           | (t, u) ->
                                               let reason =
                                                 let uu____7111 =
                                                   FStar_Ident.string_of_lid
                                                     ed.FStar_Syntax_Syntax.mname in
                                                 let uu____7112 =
                                                   FStar_Ident.string_of_lid
                                                     act1.FStar_Syntax_Syntax.action_name in
                                                 FStar_Util.format2
                                                   "implicit for return type of action %s:%s"
                                                   uu____7111 uu____7112 in
                                               let uu____7113 =
                                                 FStar_TypeChecker_Util.new_implicit_var
                                                   reason r env2 t in
                                               (match uu____7113 with
                                                | (a_tm, uu____7133, g_tm) ->
                                                    let uu____7147 =
                                                      fresh_repr r env2 u
                                                        a_tm in
                                                    (match uu____7147 with
                                                     | (repr1, g) ->
                                                         let uu____7160 =
                                                           let uu____7163 =
                                                             let uu____7166 =
                                                               let uu____7169
                                                                 =
                                                                 FStar_TypeChecker_Env.new_u_univ
                                                                   () in
                                                               FStar_All.pipe_right
                                                                 uu____7169
                                                                 (fun
                                                                    uu____7172
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____7172) in
                                                             FStar_Syntax_Syntax.mk_Total'
                                                               repr1
                                                               uu____7166 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7163 in
                                                         let uu____7173 =
                                                           FStar_TypeChecker_Env.conj_guard
                                                             g g_tm in
                                                         (uu____7160,
                                                           uu____7173))))
                                      | uu____7176 ->
                                          let uu____7177 =
                                            let uu____7182 =
                                              let uu____7183 =
                                                FStar_Ident.string_of_lid
                                                  ed.FStar_Syntax_Syntax.mname in
                                              let uu____7184 =
                                                FStar_Ident.string_of_lid
                                                  act1.FStar_Syntax_Syntax.action_name in
                                              let uu____7185 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.format3
                                                "Unexpected non-function type for action %s:%s (%s)"
                                                uu____7183 uu____7184
                                                uu____7185 in
                                            (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                              uu____7182) in
                                          FStar_Errors.raise_error uu____7177
                                            r in
                                    match uu____7055 with
                                    | (k, g_k) ->
                                        ((let uu____7199 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____7199
                                          then
                                            let uu____7200 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print1
                                              "Expected action type: %s\n"
                                              uu____7200
                                          else ());
                                         (let g =
                                            FStar_TypeChecker_Rel.teq env1
                                              act_typ1 k in
                                          FStar_List.iter
                                            (FStar_TypeChecker_Rel.force_trivial_guard
                                               env1) [g_t; g_d; g_k; g];
                                          (let uu____7205 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1)
                                               (FStar_Options.Other
                                                  "LayeredEffectsTc") in
                                           if uu____7205
                                           then
                                             let uu____7206 =
                                               FStar_Syntax_Print.term_to_string
                                                 k in
                                             FStar_Util.print1
                                               "Expected action type after unification: %s\n"
                                               uu____7206
                                           else ());
                                          (let act_typ2 =
                                             let err_msg t =
                                               let uu____7215 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____7216 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               let uu____7217 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t in
                                               FStar_Util.format3
                                                 "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                 uu____7215 uu____7216
                                                 uu____7217 in
                                             let repr_args t =
                                               let uu____7236 =
                                                 let uu____7237 =
                                                   FStar_Syntax_Subst.compress
                                                     t in
                                                 uu____7237.FStar_Syntax_Syntax.n in
                                               match uu____7236 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (head, a::is) ->
                                                   let uu____7289 =
                                                     let uu____7290 =
                                                       FStar_Syntax_Subst.compress
                                                         head in
                                                     uu____7290.FStar_Syntax_Syntax.n in
                                                   (match uu____7289 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (uu____7299, us) ->
                                                        (us,
                                                          (FStar_Pervasives_Native.fst
                                                             a), is)
                                                    | uu____7309 ->
                                                        let uu____7310 =
                                                          let uu____7315 =
                                                            err_msg t in
                                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                            uu____7315) in
                                                        FStar_Errors.raise_error
                                                          uu____7310 r)
                                               | uu____7322 ->
                                                   let uu____7323 =
                                                     let uu____7328 =
                                                       err_msg t in
                                                     (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                       uu____7328) in
                                                   FStar_Errors.raise_error
                                                     uu____7323 r in
                                             let k1 =
                                               FStar_TypeChecker_Normalize.normalize
                                                 [FStar_TypeChecker_Env.Beta]
                                                 env1 k in
                                             let uu____7336 =
                                               let uu____7337 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____7337.FStar_Syntax_Syntax.n in
                                             match uu____7336 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs, c) ->
                                                 let uu____7362 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c in
                                                 (match uu____7362 with
                                                  | (bs1, c1) ->
                                                      let uu____7369 =
                                                        repr_args
                                                          (FStar_Syntax_Util.comp_result
                                                             c1) in
                                                      (match uu____7369 with
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
                                                           let uu____7380 =
                                                             FStar_Syntax_Syntax.mk_Comp
                                                               ct in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7380))
                                             | uu____7383 ->
                                                 let uu____7384 =
                                                   let uu____7389 =
                                                     err_msg k1 in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____7389) in
                                                 FStar_Errors.raise_error
                                                   uu____7384 r in
                                           (let uu____7391 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env1)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____7391
                                            then
                                              let uu____7392 =
                                                FStar_Syntax_Print.term_to_string
                                                  act_typ2 in
                                              FStar_Util.print1
                                                "Action type after injecting it into the monad: %s\n"
                                                uu____7392
                                            else ());
                                           (let act2 =
                                              let uu____7395 =
                                                FStar_TypeChecker_Generalize.generalize_universes
                                                  env1 act_defn in
                                              match uu____7395 with
                                              | (us, act_defn1) ->
                                                  if
                                                    act1.FStar_Syntax_Syntax.action_univs
                                                      = []
                                                  then
                                                    let uu___749_7408 = act1 in
                                                    let uu____7409 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        us act_typ2 in
                                                    {
                                                      FStar_Syntax_Syntax.action_name
                                                        =
                                                        (uu___749_7408.FStar_Syntax_Syntax.action_name);
                                                      FStar_Syntax_Syntax.action_unqualified_name
                                                        =
                                                        (uu___749_7408.FStar_Syntax_Syntax.action_unqualified_name);
                                                      FStar_Syntax_Syntax.action_univs
                                                        = us;
                                                      FStar_Syntax_Syntax.action_params
                                                        =
                                                        (uu___749_7408.FStar_Syntax_Syntax.action_params);
                                                      FStar_Syntax_Syntax.action_defn
                                                        = act_defn1;
                                                      FStar_Syntax_Syntax.action_typ
                                                        = uu____7409
                                                    }
                                                  else
                                                    (let uu____7411 =
                                                       ((FStar_List.length us)
                                                          =
                                                          (FStar_List.length
                                                             act1.FStar_Syntax_Syntax.action_univs))
                                                         &&
                                                         (FStar_List.forall2
                                                            (fun u1 ->
                                                               fun u2 ->
                                                                 let uu____7417
                                                                   =
                                                                   FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2 in
                                                                 uu____7417 =
                                                                   Prims.int_zero)
                                                            us
                                                            act1.FStar_Syntax_Syntax.action_univs) in
                                                     if uu____7411
                                                     then
                                                       let uu___754_7418 =
                                                         act1 in
                                                       let uu____7419 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           act1.FStar_Syntax_Syntax.action_univs
                                                           act_typ2 in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___754_7418.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___754_7418.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           =
                                                           (uu___754_7418.FStar_Syntax_Syntax.action_univs);
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___754_7418.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____7419
                                                       }
                                                     else
                                                       (let uu____7421 =
                                                          let uu____7426 =
                                                            let uu____7427 =
                                                              FStar_Ident.string_of_lid
                                                                ed.FStar_Syntax_Syntax.mname in
                                                            let uu____7428 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____7429 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                us in
                                                            let uu____7430 =
                                                              FStar_Syntax_Print.univ_names_to_string
                                                                act1.FStar_Syntax_Syntax.action_univs in
                                                            FStar_Util.format4
                                                              "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                              uu____7427
                                                              uu____7428
                                                              uu____7429
                                                              uu____7430 in
                                                          (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                            uu____7426) in
                                                        FStar_Errors.raise_error
                                                          uu____7421 r)) in
                                            act2))))))))) in
                 let tschemes_of uu____7452 =
                   match uu____7452 with | (us, t, ty) -> ((us, t), (us, ty)) in
                 let combinators =
                   let uu____7497 =
                     let uu____7498 = tschemes_of repr in
                     let uu____7503 = tschemes_of return_repr in
                     let uu____7508 = tschemes_of bind_repr in
                     let uu____7513 = tschemes_of stronger_repr in
                     let uu____7518 = tschemes_of if_then_else in
                     {
                       FStar_Syntax_Syntax.l_repr = uu____7498;
                       FStar_Syntax_Syntax.l_return = uu____7503;
                       FStar_Syntax_Syntax.l_bind = uu____7508;
                       FStar_Syntax_Syntax.l_subcomp = uu____7513;
                       FStar_Syntax_Syntax.l_if_then_else = uu____7518
                     } in
                   FStar_Syntax_Syntax.Layered_eff uu____7497 in
                 let uu___763_7523 = ed in
                 let uu____7524 =
                   FStar_List.map (tc_action env0)
                     ed.FStar_Syntax_Syntax.actions in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___763_7523.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___763_7523.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs =
                     (uu___763_7523.FStar_Syntax_Syntax.univs);
                   FStar_Syntax_Syntax.binders =
                     (uu___763_7523.FStar_Syntax_Syntax.binders);
                   FStar_Syntax_Syntax.signature =
                     (let uu____7531 = signature in
                      match uu____7531 with | (us, t, uu____7546) -> (us, t));
                   FStar_Syntax_Syntax.combinators = combinators;
                   FStar_Syntax_Syntax.actions = uu____7524;
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___763_7523.FStar_Syntax_Syntax.eff_attrs)
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
          (let uu____7592 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
               (FStar_Options.Other "ED") in
           if uu____7592
           then
             let uu____7593 = FStar_Syntax_Print.eff_decl_to_string false ed in
             FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____7593
           else ());
          (let uu____7595 =
             let uu____7600 =
               FStar_Syntax_Subst.univ_var_opening
                 ed.FStar_Syntax_Syntax.univs in
             match uu____7600 with
             | (ed_univs_subst, ed_univs) ->
                 let bs =
                   let uu____7624 =
                     FStar_Syntax_Subst.subst_binders ed_univs_subst
                       ed.FStar_Syntax_Syntax.binders in
                   FStar_Syntax_Subst.open_binders uu____7624 in
                 let uu____7625 =
                   let uu____7632 =
                     FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                   FStar_TypeChecker_TcTerm.tc_tparams uu____7632 bs in
                 (match uu____7625 with
                  | (bs1, uu____7638, uu____7639) ->
                      let uu____7640 =
                        let tmp_t =
                          let uu____7650 =
                            let uu____7653 =
                              FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                                (fun uu____7658 ->
                                   FStar_Pervasives_Native.Some uu____7658) in
                            FStar_Syntax_Syntax.mk_Total'
                              FStar_Syntax_Syntax.t_unit uu____7653 in
                          FStar_Syntax_Util.arrow bs1 uu____7650 in
                        let uu____7659 =
                          FStar_TypeChecker_Generalize.generalize_universes
                            env0 tmp_t in
                        match uu____7659 with
                        | (us, tmp_t1) ->
                            let uu____7676 =
                              let uu____7677 =
                                let uu____7678 =
                                  FStar_All.pipe_right tmp_t1
                                    FStar_Syntax_Util.arrow_formals in
                                FStar_All.pipe_right uu____7678
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____7677
                                FStar_Syntax_Subst.close_binders in
                            (us, uu____7676) in
                      (match uu____7640 with
                       | (us, bs2) ->
                           (match ed_univs with
                            | [] -> (us, bs2)
                            | uu____7715 ->
                                let uu____7718 =
                                  ((FStar_List.length ed_univs) =
                                     (FStar_List.length us))
                                    &&
                                    (FStar_List.forall2
                                       (fun u1 ->
                                          fun u2 ->
                                            let uu____7724 =
                                              FStar_Syntax_Syntax.order_univ_name
                                                u1 u2 in
                                            uu____7724 = Prims.int_zero)
                                       ed_univs us) in
                                if uu____7718
                                then (us, bs2)
                                else
                                  (let uu____7730 =
                                     let uu____7735 =
                                       let uu____7736 =
                                         FStar_Ident.string_of_lid
                                           ed.FStar_Syntax_Syntax.mname in
                                       let uu____7737 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length ed_univs) in
                                       let uu____7738 =
                                         FStar_Util.string_of_int
                                           (FStar_List.length us) in
                                       FStar_Util.format3
                                         "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                         uu____7736 uu____7737 uu____7738 in
                                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                       uu____7735) in
                                   let uu____7739 =
                                     FStar_Ident.range_of_lid
                                       ed.FStar_Syntax_Syntax.mname in
                                   FStar_Errors.raise_error uu____7730
                                     uu____7739)))) in
           match uu____7595 with
           | (us, bs) ->
               let ed1 =
                 let uu___798_7747 = ed in
                 {
                   FStar_Syntax_Syntax.mname =
                     (uu___798_7747.FStar_Syntax_Syntax.mname);
                   FStar_Syntax_Syntax.cattributes =
                     (uu___798_7747.FStar_Syntax_Syntax.cattributes);
                   FStar_Syntax_Syntax.univs = us;
                   FStar_Syntax_Syntax.binders = bs;
                   FStar_Syntax_Syntax.signature =
                     (uu___798_7747.FStar_Syntax_Syntax.signature);
                   FStar_Syntax_Syntax.combinators =
                     (uu___798_7747.FStar_Syntax_Syntax.combinators);
                   FStar_Syntax_Syntax.actions =
                     (uu___798_7747.FStar_Syntax_Syntax.actions);
                   FStar_Syntax_Syntax.eff_attrs =
                     (uu___798_7747.FStar_Syntax_Syntax.eff_attrs)
                 } in
               let uu____7748 = FStar_Syntax_Subst.univ_var_opening us in
               (match uu____7748 with
                | (ed_univs_subst, ed_univs) ->
                    let uu____7767 =
                      let uu____7772 =
                        FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                      FStar_Syntax_Subst.open_binders' uu____7772 in
                    (match uu____7767 with
                     | (ed_bs, ed_bs_subst) ->
                         let ed2 =
                           let op uu____7793 =
                             match uu____7793 with
                             | (us1, t) ->
                                 let t1 =
                                   let uu____7813 =
                                     FStar_Syntax_Subst.shift_subst
                                       ((FStar_List.length ed_bs) +
                                          (FStar_List.length us1))
                                       ed_univs_subst in
                                   FStar_Syntax_Subst.subst uu____7813 t in
                                 let uu____7822 =
                                   let uu____7823 =
                                     FStar_Syntax_Subst.shift_subst
                                       (FStar_List.length us1) ed_bs_subst in
                                   FStar_Syntax_Subst.subst uu____7823 t1 in
                                 (us1, uu____7822) in
                           let uu___812_7828 = ed1 in
                           let uu____7829 =
                             op ed1.FStar_Syntax_Syntax.signature in
                           let uu____7830 =
                             FStar_Syntax_Util.apply_eff_combinators op
                               ed1.FStar_Syntax_Syntax.combinators in
                           let uu____7831 =
                             FStar_List.map
                               (fun a ->
                                  let uu___815_7839 = a in
                                  let uu____7840 =
                                    let uu____7841 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_defn)) in
                                    FStar_Pervasives_Native.snd uu____7841 in
                                  let uu____7852 =
                                    let uu____7853 =
                                      op
                                        ((a.FStar_Syntax_Syntax.action_univs),
                                          (a.FStar_Syntax_Syntax.action_typ)) in
                                    FStar_Pervasives_Native.snd uu____7853 in
                                  {
                                    FStar_Syntax_Syntax.action_name =
                                      (uu___815_7839.FStar_Syntax_Syntax.action_name);
                                    FStar_Syntax_Syntax.action_unqualified_name
                                      =
                                      (uu___815_7839.FStar_Syntax_Syntax.action_unqualified_name);
                                    FStar_Syntax_Syntax.action_univs =
                                      (uu___815_7839.FStar_Syntax_Syntax.action_univs);
                                    FStar_Syntax_Syntax.action_params =
                                      (uu___815_7839.FStar_Syntax_Syntax.action_params);
                                    FStar_Syntax_Syntax.action_defn =
                                      uu____7840;
                                    FStar_Syntax_Syntax.action_typ =
                                      uu____7852
                                  }) ed1.FStar_Syntax_Syntax.actions in
                           {
                             FStar_Syntax_Syntax.mname =
                               (uu___812_7828.FStar_Syntax_Syntax.mname);
                             FStar_Syntax_Syntax.cattributes =
                               (uu___812_7828.FStar_Syntax_Syntax.cattributes);
                             FStar_Syntax_Syntax.univs =
                               (uu___812_7828.FStar_Syntax_Syntax.univs);
                             FStar_Syntax_Syntax.binders =
                               (uu___812_7828.FStar_Syntax_Syntax.binders);
                             FStar_Syntax_Syntax.signature = uu____7829;
                             FStar_Syntax_Syntax.combinators = uu____7830;
                             FStar_Syntax_Syntax.actions = uu____7831;
                             FStar_Syntax_Syntax.eff_attrs =
                               (uu___812_7828.FStar_Syntax_Syntax.eff_attrs)
                           } in
                         ((let uu____7865 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "ED") in
                           if uu____7865
                           then
                             let uu____7866 =
                               FStar_Syntax_Print.eff_decl_to_string false
                                 ed2 in
                             FStar_Util.print1
                               "After typechecking binders eff_decl: \n\t%s\n"
                               uu____7866
                           else ());
                          (let env =
                             let uu____7869 =
                               FStar_TypeChecker_Env.push_univ_vars env0
                                 ed_univs in
                             FStar_TypeChecker_Env.push_binders uu____7869
                               ed_bs in
                           let check_and_gen' comb n env_opt uu____7902 k =
                             match uu____7902 with
                             | (us1, t) ->
                                 let env1 =
                                   if FStar_Util.is_some env_opt
                                   then
                                     FStar_All.pipe_right env_opt
                                       FStar_Util.must
                                   else env in
                                 let uu____7918 =
                                   FStar_Syntax_Subst.open_univ_vars us1 t in
                                 (match uu____7918 with
                                  | (us2, t1) ->
                                      let t2 =
                                        match k with
                                        | FStar_Pervasives_Native.Some k1 ->
                                            let uu____7927 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                              uu____7927 t1 k1
                                        | FStar_Pervasives_Native.None ->
                                            let uu____7928 =
                                              let uu____7935 =
                                                FStar_TypeChecker_Env.push_univ_vars
                                                  env1 us2 in
                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                uu____7935 t1 in
                                            (match uu____7928 with
                                             | (t2, uu____7937, g) ->
                                                 (FStar_TypeChecker_Rel.force_trivial_guard
                                                    env1 g;
                                                  t2)) in
                                      let uu____7940 =
                                        FStar_TypeChecker_Generalize.generalize_universes
                                          env1 t2 in
                                      (match uu____7940 with
                                       | (g_us, t3) ->
                                           (if (FStar_List.length g_us) <> n
                                            then
                                              (let error =
                                                 let uu____7953 =
                                                   FStar_Ident.string_of_lid
                                                     ed2.FStar_Syntax_Syntax.mname in
                                                 let uu____7954 =
                                                   FStar_Util.string_of_int n in
                                                 let uu____7955 =
                                                   let uu____7956 =
                                                     FStar_All.pipe_right
                                                       g_us FStar_List.length in
                                                   FStar_All.pipe_right
                                                     uu____7956
                                                     FStar_Util.string_of_int in
                                                 FStar_Util.format4
                                                   "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                   uu____7953 comb uu____7954
                                                   uu____7955 in
                                               FStar_Errors.raise_error
                                                 (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                   error)
                                                 t3.FStar_Syntax_Syntax.pos)
                                            else ();
                                            (match us2 with
                                             | [] -> (g_us, t3)
                                             | uu____7964 ->
                                                 let uu____7965 =
                                                   ((FStar_List.length us2) =
                                                      (FStar_List.length g_us))
                                                     &&
                                                     (FStar_List.forall2
                                                        (fun u1 ->
                                                           fun u2 ->
                                                             let uu____7971 =
                                                               FStar_Syntax_Syntax.order_univ_name
                                                                 u1 u2 in
                                                             uu____7971 =
                                                               Prims.int_zero)
                                                        us2 g_us) in
                                                 if uu____7965
                                                 then (g_us, t3)
                                                 else
                                                   (let uu____7977 =
                                                      let uu____7982 =
                                                        let uu____7983 =
                                                          FStar_Ident.string_of_lid
                                                            ed2.FStar_Syntax_Syntax.mname in
                                                        let uu____7984 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               us2) in
                                                        let uu____7985 =
                                                          FStar_Util.string_of_int
                                                            (FStar_List.length
                                                               g_us) in
                                                        FStar_Util.format4
                                                          "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                          uu____7983 comb
                                                          uu____7984
                                                          uu____7985 in
                                                      (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                        uu____7982) in
                                                    FStar_Errors.raise_error
                                                      uu____7977
                                                      t3.FStar_Syntax_Syntax.pos))))) in
                           let signature =
                             check_and_gen' "signature" Prims.int_one
                               FStar_Pervasives_Native.None
                               ed2.FStar_Syntax_Syntax.signature
                               FStar_Pervasives_Native.None in
                           (let uu____7988 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "ED") in
                            if uu____7988
                            then
                              let uu____7989 =
                                FStar_Syntax_Print.tscheme_to_string
                                  signature in
                              FStar_Util.print1 "Typechecked signature: %s\n"
                                uu____7989
                            else ());
                           (let fresh_a_and_wp uu____8002 =
                              let fail t =
                                let uu____8015 =
                                  FStar_TypeChecker_Err.unexpected_signature_for_monad
                                    env ed2.FStar_Syntax_Syntax.mname t in
                                FStar_Errors.raise_error uu____8015
                                  (FStar_Pervasives_Native.snd
                                     ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                              let uu____8030 =
                                FStar_TypeChecker_Env.inst_tscheme signature in
                              match uu____8030 with
                              | (uu____8041, signature1) ->
                                  let uu____8043 =
                                    let uu____8044 =
                                      FStar_Syntax_Subst.compress signature1 in
                                    uu____8044.FStar_Syntax_Syntax.n in
                                  (match uu____8043 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs1, uu____8054) ->
                                       let bs2 =
                                         FStar_Syntax_Subst.open_binders bs1 in
                                       (match bs2 with
                                        | (a, uu____8083)::(wp, uu____8085)::[]
                                            ->
                                            (a,
                                              (wp.FStar_Syntax_Syntax.sort))
                                        | uu____8114 -> fail signature1)
                                   | uu____8115 -> fail signature1) in
                            let log_combinator s ts =
                              let uu____8127 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  (FStar_Options.Other "ED") in
                              if uu____8127
                              then
                                let uu____8128 =
                                  FStar_Ident.string_of_lid
                                    ed2.FStar_Syntax_Syntax.mname in
                                let uu____8129 =
                                  FStar_Syntax_Print.tscheme_to_string ts in
                                FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                  uu____8128 s uu____8129
                              else () in
                            let ret_wp =
                              let uu____8132 = fresh_a_and_wp () in
                              match uu____8132 with
                              | (a, wp_sort) ->
                                  let k =
                                    let uu____8148 =
                                      let uu____8157 =
                                        FStar_Syntax_Syntax.mk_binder a in
                                      let uu____8164 =
                                        let uu____8173 =
                                          let uu____8180 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          FStar_Syntax_Syntax.null_binder
                                            uu____8180 in
                                        [uu____8173] in
                                      uu____8157 :: uu____8164 in
                                    let uu____8199 =
                                      FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                    FStar_Syntax_Util.arrow uu____8148
                                      uu____8199 in
                                  let uu____8202 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_return_vc_combinator in
                                  check_and_gen' "ret_wp" Prims.int_one
                                    FStar_Pervasives_Native.None uu____8202
                                    (FStar_Pervasives_Native.Some k) in
                            log_combinator "ret_wp" ret_wp;
                            (let bind_wp =
                               let uu____8213 = fresh_a_and_wp () in
                               match uu____8213 with
                               | (a, wp_sort_a) ->
                                   let uu____8226 = fresh_a_and_wp () in
                                   (match uu____8226 with
                                    | (b, wp_sort_b) ->
                                        let wp_sort_a_b =
                                          let uu____8242 =
                                            let uu____8251 =
                                              let uu____8258 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  a in
                                              FStar_Syntax_Syntax.null_binder
                                                uu____8258 in
                                            [uu____8251] in
                                          let uu____8271 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8242
                                            uu____8271 in
                                        let k =
                                          let uu____8277 =
                                            let uu____8286 =
                                              FStar_Syntax_Syntax.null_binder
                                                FStar_Syntax_Syntax.t_range in
                                            let uu____8293 =
                                              let uu____8302 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  a in
                                              let uu____8309 =
                                                let uu____8318 =
                                                  FStar_Syntax_Syntax.mk_binder
                                                    b in
                                                let uu____8325 =
                                                  let uu____8334 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a in
                                                  let uu____8341 =
                                                    let uu____8350 =
                                                      FStar_Syntax_Syntax.null_binder
                                                        wp_sort_a_b in
                                                    [uu____8350] in
                                                  uu____8334 :: uu____8341 in
                                                uu____8318 :: uu____8325 in
                                              uu____8302 :: uu____8309 in
                                            uu____8286 :: uu____8293 in
                                          let uu____8393 =
                                            FStar_Syntax_Syntax.mk_Total
                                              wp_sort_b in
                                          FStar_Syntax_Util.arrow uu____8277
                                            uu____8393 in
                                        let uu____8396 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_bind_vc_combinator in
                                        check_and_gen' "bind_wp"
                                          (Prims.of_int (2))
                                          FStar_Pervasives_Native.None
                                          uu____8396
                                          (FStar_Pervasives_Native.Some k)) in
                             log_combinator "bind_wp" bind_wp;
                             (let stronger =
                                let uu____8407 = fresh_a_and_wp () in
                                match uu____8407 with
                                | (a, wp_sort_a) ->
                                    let uu____8420 =
                                      FStar_Syntax_Util.type_u () in
                                    (match uu____8420 with
                                     | (t, uu____8426) ->
                                         let k =
                                           let uu____8430 =
                                             let uu____8439 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a in
                                             let uu____8446 =
                                               let uu____8455 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               let uu____8462 =
                                                 let uu____8471 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____8471] in
                                               uu____8455 :: uu____8462 in
                                             uu____8439 :: uu____8446 in
                                           let uu____8502 =
                                             FStar_Syntax_Syntax.mk_Total t in
                                           FStar_Syntax_Util.arrow uu____8430
                                             uu____8502 in
                                         let uu____8505 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_stronger_vc_combinator in
                                         check_and_gen' "stronger"
                                           Prims.int_one
                                           FStar_Pervasives_Native.None
                                           uu____8505
                                           (FStar_Pervasives_Native.Some k)) in
                              log_combinator "stronger" stronger;
                              (let if_then_else =
                                 let uu____8516 = fresh_a_and_wp () in
                                 match uu____8516 with
                                 | (a, wp_sort_a) ->
                                     let p =
                                       let uu____8530 =
                                         let uu____8533 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____8533 in
                                       let uu____8534 =
                                         let uu____8535 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____8535
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____8530
                                         uu____8534 in
                                     let k =
                                       let uu____8547 =
                                         let uu____8556 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____8563 =
                                           let uu____8572 =
                                             FStar_Syntax_Syntax.mk_binder p in
                                           let uu____8579 =
                                             let uu____8588 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____8595 =
                                               let uu____8604 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____8604] in
                                             uu____8588 :: uu____8595 in
                                           uu____8572 :: uu____8579 in
                                         uu____8556 :: uu____8563 in
                                       let uu____8641 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____8547
                                         uu____8641 in
                                     let uu____8644 =
                                       let uu____8649 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                       FStar_All.pipe_right uu____8649
                                         FStar_Util.must in
                                     check_and_gen' "if_then_else"
                                       Prims.int_one
                                       FStar_Pervasives_Native.None
                                       uu____8644
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "if_then_else" if_then_else;
                               (let ite_wp =
                                  let uu____8678 = fresh_a_and_wp () in
                                  match uu____8678 with
                                  | (a, wp_sort_a) ->
                                      let k =
                                        let uu____8694 =
                                          let uu____8703 =
                                            FStar_Syntax_Syntax.mk_binder a in
                                          let uu____8710 =
                                            let uu____8719 =
                                              FStar_Syntax_Syntax.null_binder
                                                wp_sort_a in
                                            [uu____8719] in
                                          uu____8703 :: uu____8710 in
                                        let uu____8744 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_a in
                                        FStar_Syntax_Util.arrow uu____8694
                                          uu____8744 in
                                      let uu____8747 =
                                        let uu____8752 =
                                          FStar_All.pipe_right ed2
                                            FStar_Syntax_Util.get_wp_ite_combinator in
                                        FStar_All.pipe_right uu____8752
                                          FStar_Util.must in
                                      check_and_gen' "ite_wp" Prims.int_one
                                        FStar_Pervasives_Native.None
                                        uu____8747
                                        (FStar_Pervasives_Native.Some k) in
                                log_combinator "ite_wp" ite_wp;
                                (let close_wp =
                                   let uu____8781 = fresh_a_and_wp () in
                                   match uu____8781 with
                                   | (a, wp_sort_a) ->
                                       let b =
                                         let uu____8795 =
                                           let uu____8798 =
                                             FStar_Ident.range_of_lid
                                               ed2.FStar_Syntax_Syntax.mname in
                                           FStar_Pervasives_Native.Some
                                             uu____8798 in
                                         let uu____8799 =
                                           let uu____8800 =
                                             FStar_Syntax_Util.type_u () in
                                           FStar_All.pipe_right uu____8800
                                             FStar_Pervasives_Native.fst in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____8795 uu____8799 in
                                       let wp_sort_b_a =
                                         let uu____8812 =
                                           let uu____8821 =
                                             let uu____8828 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 b in
                                             FStar_Syntax_Syntax.null_binder
                                               uu____8828 in
                                           [uu____8821] in
                                         let uu____8841 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____8812
                                           uu____8841 in
                                       let k =
                                         let uu____8847 =
                                           let uu____8856 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____8863 =
                                             let uu____8872 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 b in
                                             let uu____8879 =
                                               let uu____8888 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_b_a in
                                               [uu____8888] in
                                             uu____8872 :: uu____8879 in
                                           uu____8856 :: uu____8863 in
                                         let uu____8919 =
                                           FStar_Syntax_Syntax.mk_Total
                                             wp_sort_a in
                                         FStar_Syntax_Util.arrow uu____8847
                                           uu____8919 in
                                       let uu____8922 =
                                         let uu____8927 =
                                           FStar_All.pipe_right ed2
                                             FStar_Syntax_Util.get_wp_close_combinator in
                                         FStar_All.pipe_right uu____8927
                                           FStar_Util.must in
                                       check_and_gen' "close_wp"
                                         (Prims.of_int (2))
                                         FStar_Pervasives_Native.None
                                         uu____8922
                                         (FStar_Pervasives_Native.Some k) in
                                 log_combinator "close_wp" close_wp;
                                 (let trivial =
                                    let uu____8940 = fresh_a_and_wp () in
                                    match uu____8940 with
                                    | (a, wp_sort_a) ->
                                        let uu____8953 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____8953 with
                                         | (t, uu____8959) ->
                                             let k =
                                               let uu____8963 =
                                                 let uu____8972 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     a in
                                                 let uu____8979 =
                                                   let uu____8988 =
                                                     FStar_Syntax_Syntax.null_binder
                                                       wp_sort_a in
                                                   [uu____8988] in
                                                 uu____8972 :: uu____8979 in
                                               let uu____9013 =
                                                 FStar_Syntax_Syntax.mk_GTotal
                                                   t in
                                               FStar_Syntax_Util.arrow
                                                 uu____8963 uu____9013 in
                                             let trivial =
                                               let uu____9017 =
                                                 let uu____9022 =
                                                   FStar_All.pipe_right ed2
                                                     FStar_Syntax_Util.get_wp_trivial_combinator in
                                                 FStar_All.pipe_right
                                                   uu____9022 FStar_Util.must in
                                               check_and_gen' "trivial"
                                                 Prims.int_one
                                                 FStar_Pervasives_Native.None
                                                 uu____9017
                                                 (FStar_Pervasives_Native.Some
                                                    k) in
                                             (log_combinator "trivial"
                                                trivial;
                                              trivial)) in
                                  let uu____9050 =
                                    let uu____9067 =
                                      FStar_All.pipe_right ed2
                                        FStar_Syntax_Util.get_eff_repr in
                                    match uu____9067 with
                                    | FStar_Pervasives_Native.None ->
                                        (FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          FStar_Pervasives_Native.None,
                                          (ed2.FStar_Syntax_Syntax.actions))
                                    | uu____9096 ->
                                        let repr =
                                          let uu____9100 = fresh_a_and_wp () in
                                          match uu____9100 with
                                          | (a, wp_sort_a) ->
                                              let uu____9113 =
                                                FStar_Syntax_Util.type_u () in
                                              (match uu____9113 with
                                               | (t, uu____9119) ->
                                                   let k =
                                                     let uu____9123 =
                                                       let uu____9132 =
                                                         FStar_Syntax_Syntax.mk_binder
                                                           a in
                                                       let uu____9139 =
                                                         let uu____9148 =
                                                           FStar_Syntax_Syntax.null_binder
                                                             wp_sort_a in
                                                         [uu____9148] in
                                                       uu____9132 ::
                                                         uu____9139 in
                                                     let uu____9173 =
                                                       FStar_Syntax_Syntax.mk_GTotal
                                                         t in
                                                     FStar_Syntax_Util.arrow
                                                       uu____9123 uu____9173 in
                                                   let uu____9176 =
                                                     let uu____9181 =
                                                       FStar_All.pipe_right
                                                         ed2
                                                         FStar_Syntax_Util.get_eff_repr in
                                                     FStar_All.pipe_right
                                                       uu____9181
                                                       FStar_Util.must in
                                                   check_and_gen' "repr"
                                                     Prims.int_one
                                                     FStar_Pervasives_Native.None
                                                     uu____9176
                                                     (FStar_Pervasives_Native.Some
                                                        k)) in
                                        (log_combinator "repr" repr;
                                         (let mk_repr' t wp =
                                            let uu____9222 =
                                              FStar_TypeChecker_Env.inst_tscheme
                                                repr in
                                            match uu____9222 with
                                            | (uu____9229, repr1) ->
                                                let repr2 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.EraseUniverses;
                                                    FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                    env repr1 in
                                                let uu____9232 =
                                                  let uu____9233 =
                                                    let uu____9250 =
                                                      let uu____9261 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9278 =
                                                        let uu____9289 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9289] in
                                                      uu____9261 ::
                                                        uu____9278 in
                                                    (repr2, uu____9250) in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____9233 in
                                                FStar_Syntax_Syntax.mk
                                                  uu____9232
                                                  FStar_Range.dummyRange in
                                          let mk_repr a wp =
                                            let uu____9355 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            mk_repr' uu____9355 wp in
                                          let destruct_repr t =
                                            let uu____9370 =
                                              let uu____9371 =
                                                FStar_Syntax_Subst.compress t in
                                              uu____9371.FStar_Syntax_Syntax.n in
                                            match uu____9370 with
                                            | FStar_Syntax_Syntax.Tm_app
                                                (uu____9382,
                                                 (t1, uu____9384)::(wp,
                                                                    uu____9386)::[])
                                                -> (t1, wp)
                                            | uu____9445 ->
                                                failwith
                                                  "Unexpected repr type" in
                                          let return_repr =
                                            let return_repr_ts =
                                              let uu____9460 =
                                                FStar_All.pipe_right ed2
                                                  FStar_Syntax_Util.get_return_repr in
                                              FStar_All.pipe_right uu____9460
                                                FStar_Util.must in
                                            let uu____9487 =
                                              fresh_a_and_wp () in
                                            match uu____9487 with
                                            | (a, uu____9495) ->
                                                let x_a =
                                                  let uu____9501 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      a in
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "x_a"
                                                    FStar_Pervasives_Native.None
                                                    uu____9501 in
                                                let res =
                                                  let wp =
                                                    let uu____9506 =
                                                      let uu____9507 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp in
                                                      FStar_All.pipe_right
                                                        uu____9507
                                                        FStar_Pervasives_Native.snd in
                                                    let uu____9516 =
                                                      let uu____9517 =
                                                        let uu____9526 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_All.pipe_right
                                                          uu____9526
                                                          FStar_Syntax_Syntax.as_arg in
                                                      let uu____9535 =
                                                        let uu____9546 =
                                                          let uu____9555 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____9555
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9546] in
                                                      uu____9517 ::
                                                        uu____9535 in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____9506 uu____9516
                                                      FStar_Range.dummyRange in
                                                  mk_repr a wp in
                                                let k =
                                                  let uu____9591 =
                                                    let uu____9600 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        a in
                                                    let uu____9607 =
                                                      let uu____9616 =
                                                        FStar_Syntax_Syntax.mk_binder
                                                          x_a in
                                                      [uu____9616] in
                                                    uu____9600 :: uu____9607 in
                                                  let uu____9641 =
                                                    FStar_Syntax_Syntax.mk_Total
                                                      res in
                                                  FStar_Syntax_Util.arrow
                                                    uu____9591 uu____9641 in
                                                let uu____9644 =
                                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                    env k in
                                                (match uu____9644 with
                                                 | (k1, uu____9652,
                                                    uu____9653) ->
                                                     let env1 =
                                                       let uu____9657 =
                                                         FStar_TypeChecker_Env.set_range
                                                           env
                                                           (FStar_Pervasives_Native.snd
                                                              return_repr_ts).FStar_Syntax_Syntax.pos in
                                                       FStar_Pervasives_Native.Some
                                                         uu____9657 in
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
                                               let uu____9667 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_bind_repr in
                                               FStar_All.pipe_right
                                                 uu____9667 FStar_Util.must in
                                             let r =
                                               let uu____9681 =
                                                 FStar_Syntax_Syntax.lid_as_fv
                                                   FStar_Parser_Const.range_0
                                                   FStar_Syntax_Syntax.delta_constant
                                                   FStar_Pervasives_Native.None in
                                               FStar_All.pipe_right
                                                 uu____9681
                                                 FStar_Syntax_Syntax.fv_to_tm in
                                             let uu____9682 =
                                               fresh_a_and_wp () in
                                             match uu____9682 with
                                             | (a, wp_sort_a) ->
                                                 let uu____9695 =
                                                   fresh_a_and_wp () in
                                                 (match uu____9695 with
                                                  | (b, wp_sort_b) ->
                                                      let wp_sort_a_b =
                                                        let uu____9711 =
                                                          let uu____9720 =
                                                            let uu____9727 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                a in
                                                            FStar_Syntax_Syntax.null_binder
                                                              uu____9727 in
                                                          [uu____9720] in
                                                        let uu____9740 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            wp_sort_b in
                                                        FStar_Syntax_Util.arrow
                                                          uu____9711
                                                          uu____9740 in
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
                                                        let uu____9746 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a in
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "x_a"
                                                          FStar_Pervasives_Native.None
                                                          uu____9746 in
                                                      let wp_g_x =
                                                        let uu____9748 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g in
                                                        let uu____9749 =
                                                          let uu____9750 =
                                                            let uu____9759 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a in
                                                            FStar_All.pipe_right
                                                              uu____9759
                                                              FStar_Syntax_Syntax.as_arg in
                                                          [uu____9750] in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____9748
                                                          uu____9749
                                                          FStar_Range.dummyRange in
                                                      let res =
                                                        let wp =
                                                          let uu____9788 =
                                                            let uu____9789 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp in
                                                            FStar_All.pipe_right
                                                              uu____9789
                                                              FStar_Pervasives_Native.snd in
                                                          let uu____9798 =
                                                            let uu____9799 =
                                                              let uu____9802
                                                                =
                                                                let uu____9805
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a in
                                                                let uu____9806
                                                                  =
                                                                  let uu____9809
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                  let uu____9810
                                                                    =
                                                                    let uu____9813
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    let uu____9814
                                                                    =
                                                                    let uu____9817
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____9817] in
                                                                    uu____9813
                                                                    ::
                                                                    uu____9814 in
                                                                  uu____9809
                                                                    ::
                                                                    uu____9810 in
                                                                uu____9805 ::
                                                                  uu____9806 in
                                                              r :: uu____9802 in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____9799 in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____9788
                                                            uu____9798
                                                            FStar_Range.dummyRange in
                                                        mk_repr b wp in
                                                      let maybe_range_arg =
                                                        let uu____9835 =
                                                          FStar_Util.for_some
                                                            (FStar_Syntax_Util.attr_eq
                                                               FStar_Syntax_Util.dm4f_bind_range_attr)
                                                            ed2.FStar_Syntax_Syntax.eff_attrs in
                                                        if uu____9835
                                                        then
                                                          let uu____9844 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          let uu____9851 =
                                                            let uu____9860 =
                                                              FStar_Syntax_Syntax.null_binder
                                                                FStar_Syntax_Syntax.t_range in
                                                            [uu____9860] in
                                                          uu____9844 ::
                                                            uu____9851
                                                        else [] in
                                                      let k =
                                                        let uu____9895 =
                                                          let uu____9904 =
                                                            let uu____9913 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                a in
                                                            let uu____9920 =
                                                              let uu____9929
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  b in
                                                              [uu____9929] in
                                                            uu____9913 ::
                                                              uu____9920 in
                                                          let uu____9954 =
                                                            let uu____9963 =
                                                              let uu____9972
                                                                =
                                                                FStar_Syntax_Syntax.mk_binder
                                                                  wp_f in
                                                              let uu____9979
                                                                =
                                                                let uu____9988
                                                                  =
                                                                  let uu____9995
                                                                    =
                                                                    let uu____9996
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                    mk_repr a
                                                                    uu____9996 in
                                                                  FStar_Syntax_Syntax.null_binder
                                                                    uu____9995 in
                                                                let uu____9997
                                                                  =
                                                                  let uu____10006
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                  let uu____10013
                                                                    =
                                                                    let uu____10022
                                                                    =
                                                                    let uu____10029
                                                                    =
                                                                    let uu____10030
                                                                    =
                                                                    let uu____10039
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____10039] in
                                                                    let uu____10058
                                                                    =
                                                                    let uu____10061
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____10061 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____10030
                                                                    uu____10058 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____10029 in
                                                                    [uu____10022] in
                                                                  uu____10006
                                                                    ::
                                                                    uu____10013 in
                                                                uu____9988 ::
                                                                  uu____9997 in
                                                              uu____9972 ::
                                                                uu____9979 in
                                                            FStar_List.append
                                                              maybe_range_arg
                                                              uu____9963 in
                                                          FStar_List.append
                                                            uu____9904
                                                            uu____9954 in
                                                        let uu____10106 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            res in
                                                        FStar_Syntax_Util.arrow
                                                          uu____9895
                                                          uu____10106 in
                                                      let uu____10109 =
                                                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                          env k in
                                                      (match uu____10109 with
                                                       | (k1, uu____10117,
                                                          uu____10118) ->
                                                           let env1 =
                                                             FStar_TypeChecker_Env.set_range
                                                               env
                                                               (FStar_Pervasives_Native.snd
                                                                  bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                           let env2 =
                                                             FStar_All.pipe_right
                                                               (let uu___1010_10128
                                                                  = env1 in
                                                                {
                                                                  FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.solver);
                                                                  FStar_TypeChecker_Env.range
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.range);
                                                                  FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.curmodule);
                                                                  FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.gamma);
                                                                  FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.gamma_sig);
                                                                  FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.gamma_cache);
                                                                  FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.modules);
                                                                  FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.expected_typ);
                                                                  FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.sigtab);
                                                                  FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.attrtab);
                                                                  FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.instantiate_imp);
                                                                  FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.effects);
                                                                  FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.generalize);
                                                                  FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.letrecs);
                                                                  FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.top_level);
                                                                  FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.check_uvars);
                                                                  FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.use_eq);
                                                                  FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.use_eq_strict);
                                                                  FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.is_iface);
                                                                  FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.admit);
                                                                  FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                  FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.lax_universes);
                                                                  FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.phase1);
                                                                  FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.failhard);
                                                                  FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.nosynth);
                                                                  FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.uvar_subtyping);
                                                                  FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.tc_term);
                                                                  FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.type_of);
                                                                  FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.universe_of);
                                                                  FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.check_type_of);
                                                                  FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.use_bv_sorts);
                                                                  FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                  FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.normalized_eff_names);
                                                                  FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.fv_delta_depths);
                                                                  FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.proof_ns);
                                                                  FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.synth_hook);
                                                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                  FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.splice);
                                                                  FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.mpreprocess);
                                                                  FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.postprocess);
                                                                  FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.identifier_info);
                                                                  FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.tc_hooks);
                                                                  FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.dsenv);
                                                                  FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.nbe);
                                                                  FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.strict_args_tab);
                                                                  FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.erasable_types_tab);
                                                                  FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (
                                                                    uu___1010_10128.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                                })
                                                               (fun
                                                                  uu____10129
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____10129) in
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
                                                (let uu____10148 =
                                                   if
                                                     act.FStar_Syntax_Syntax.action_univs
                                                       = []
                                                   then (env, act)
                                                   else
                                                     (let uu____10160 =
                                                        FStar_Syntax_Subst.univ_var_opening
                                                          act.FStar_Syntax_Syntax.action_univs in
                                                      match uu____10160 with
                                                      | (usubst, uvs) ->
                                                          let uu____10183 =
                                                            FStar_TypeChecker_Env.push_univ_vars
                                                              env uvs in
                                                          let uu____10184 =
                                                            let uu___1023_10185
                                                              = act in
                                                            let uu____10186 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_defn in
                                                            let uu____10187 =
                                                              FStar_Syntax_Subst.subst
                                                                usubst
                                                                act.FStar_Syntax_Syntax.action_typ in
                                                            {
                                                              FStar_Syntax_Syntax.action_name
                                                                =
                                                                (uu___1023_10185.FStar_Syntax_Syntax.action_name);
                                                              FStar_Syntax_Syntax.action_unqualified_name
                                                                =
                                                                (uu___1023_10185.FStar_Syntax_Syntax.action_unqualified_name);
                                                              FStar_Syntax_Syntax.action_univs
                                                                = uvs;
                                                              FStar_Syntax_Syntax.action_params
                                                                =
                                                                (uu___1023_10185.FStar_Syntax_Syntax.action_params);
                                                              FStar_Syntax_Syntax.action_defn
                                                                = uu____10186;
                                                              FStar_Syntax_Syntax.action_typ
                                                                = uu____10187
                                                            } in
                                                          (uu____10183,
                                                            uu____10184)) in
                                                 match uu____10148 with
                                                 | (env1, act1) ->
                                                     let act_typ =
                                                       let uu____10191 =
                                                         let uu____10192 =
                                                           FStar_Syntax_Subst.compress
                                                             act1.FStar_Syntax_Syntax.action_typ in
                                                         uu____10192.FStar_Syntax_Syntax.n in
                                                       match uu____10191 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let c1 =
                                                             FStar_Syntax_Util.comp_to_comp_typ
                                                               c in
                                                           let uu____10218 =
                                                             FStar_Ident.lid_equals
                                                               c1.FStar_Syntax_Syntax.effect_name
                                                               ed2.FStar_Syntax_Syntax.mname in
                                                           if uu____10218
                                                           then
                                                             let uu____10219
                                                               =
                                                               let uu____10222
                                                                 =
                                                                 let uu____10223
                                                                   =
                                                                   let uu____10224
                                                                    =
                                                                    FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                   FStar_Pervasives_Native.fst
                                                                    uu____10224 in
                                                                 mk_repr'
                                                                   c1.FStar_Syntax_Syntax.result_typ
                                                                   uu____10223 in
                                                               FStar_Syntax_Syntax.mk_Total
                                                                 uu____10222 in
                                                             FStar_Syntax_Util.arrow
                                                               bs1
                                                               uu____10219
                                                           else
                                                             act1.FStar_Syntax_Syntax.action_typ
                                                       | uu____10246 ->
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                     let uu____10247 =
                                                       FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                         env1 act_typ in
                                                     (match uu____10247 with
                                                      | (act_typ1,
                                                         uu____10255, g_t) ->
                                                          let env' =
                                                            let uu___1040_10258
                                                              =
                                                              FStar_TypeChecker_Env.set_expected_typ
                                                                env1 act_typ1 in
                                                            {
                                                              FStar_TypeChecker_Env.solver
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.solver);
                                                              FStar_TypeChecker_Env.range
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.range);
                                                              FStar_TypeChecker_Env.curmodule
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.curmodule);
                                                              FStar_TypeChecker_Env.gamma
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.gamma);
                                                              FStar_TypeChecker_Env.gamma_sig
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.gamma_sig);
                                                              FStar_TypeChecker_Env.gamma_cache
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.gamma_cache);
                                                              FStar_TypeChecker_Env.modules
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.modules);
                                                              FStar_TypeChecker_Env.expected_typ
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.expected_typ);
                                                              FStar_TypeChecker_Env.sigtab
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.sigtab);
                                                              FStar_TypeChecker_Env.attrtab
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.attrtab);
                                                              FStar_TypeChecker_Env.instantiate_imp
                                                                = false;
                                                              FStar_TypeChecker_Env.effects
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.effects);
                                                              FStar_TypeChecker_Env.generalize
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.generalize);
                                                              FStar_TypeChecker_Env.letrecs
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.letrecs);
                                                              FStar_TypeChecker_Env.top_level
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.top_level);
                                                              FStar_TypeChecker_Env.check_uvars
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.check_uvars);
                                                              FStar_TypeChecker_Env.use_eq
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.use_eq);
                                                              FStar_TypeChecker_Env.use_eq_strict
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.use_eq_strict);
                                                              FStar_TypeChecker_Env.is_iface
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.is_iface);
                                                              FStar_TypeChecker_Env.admit
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.admit);
                                                              FStar_TypeChecker_Env.lax
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.lax);
                                                              FStar_TypeChecker_Env.lax_universes
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.lax_universes);
                                                              FStar_TypeChecker_Env.phase1
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.phase1);
                                                              FStar_TypeChecker_Env.failhard
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.failhard);
                                                              FStar_TypeChecker_Env.nosynth
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.nosynth);
                                                              FStar_TypeChecker_Env.uvar_subtyping
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.uvar_subtyping);
                                                              FStar_TypeChecker_Env.tc_term
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.tc_term);
                                                              FStar_TypeChecker_Env.type_of
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.type_of);
                                                              FStar_TypeChecker_Env.universe_of
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.universe_of);
                                                              FStar_TypeChecker_Env.check_type_of
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.check_type_of);
                                                              FStar_TypeChecker_Env.use_bv_sorts
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.use_bv_sorts);
                                                              FStar_TypeChecker_Env.qtbl_name_and_index
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                              FStar_TypeChecker_Env.normalized_eff_names
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.normalized_eff_names);
                                                              FStar_TypeChecker_Env.fv_delta_depths
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.fv_delta_depths);
                                                              FStar_TypeChecker_Env.proof_ns
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.proof_ns);
                                                              FStar_TypeChecker_Env.synth_hook
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.synth_hook);
                                                              FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                              FStar_TypeChecker_Env.splice
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.splice);
                                                              FStar_TypeChecker_Env.mpreprocess
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.mpreprocess);
                                                              FStar_TypeChecker_Env.postprocess
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.postprocess);
                                                              FStar_TypeChecker_Env.identifier_info
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.identifier_info);
                                                              FStar_TypeChecker_Env.tc_hooks
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.tc_hooks);
                                                              FStar_TypeChecker_Env.dsenv
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.dsenv);
                                                              FStar_TypeChecker_Env.nbe
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.nbe);
                                                              FStar_TypeChecker_Env.strict_args_tab
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.strict_args_tab);
                                                              FStar_TypeChecker_Env.erasable_types_tab
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.erasable_types_tab);
                                                              FStar_TypeChecker_Env.enable_defer_to_tac
                                                                =
                                                                (uu___1040_10258.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                            } in
                                                          ((let uu____10260 =
                                                              FStar_TypeChecker_Env.debug
                                                                env1
                                                                (FStar_Options.Other
                                                                   "ED") in
                                                            if uu____10260
                                                            then
                                                              let uu____10261
                                                                =
                                                                FStar_Ident.string_of_lid
                                                                  act1.FStar_Syntax_Syntax.action_name in
                                                              let uu____10262
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act1.FStar_Syntax_Syntax.action_defn in
                                                              let uu____10263
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  act_typ1 in
                                                              FStar_Util.print3
                                                                "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                                uu____10261
                                                                uu____10262
                                                                uu____10263
                                                            else ());
                                                           (let uu____10265 =
                                                              FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                env'
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            match uu____10265
                                                            with
                                                            | (act_defn,
                                                               uu____10273,
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
                                                                let uu____10277
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
                                                                    let uu____10313
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10313
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10325)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10332
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10332 in
                                                                    let uu____10335
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10335
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10349,
                                                                    g) ->
                                                                    (k1, g)))
                                                                  | uu____10353
                                                                    ->
                                                                    let uu____10354
                                                                    =
                                                                    let uu____10359
                                                                    =
                                                                    let uu____10360
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10361
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10360
                                                                    uu____10361 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10359) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10354
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                                (match uu____10277
                                                                 with
                                                                 | (expected_k,
                                                                    g_k) ->
                                                                    let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                    ((
                                                                    let uu____10376
                                                                    =
                                                                    let uu____10377
                                                                    =
                                                                    let uu____10378
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10378 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10377 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10376);
                                                                    (let act_typ3
                                                                    =
                                                                    let uu____10380
                                                                    =
                                                                    let uu____10381
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10381.FStar_Syntax_Syntax.n in
                                                                    match uu____10380
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10406
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10406
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10413
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10413
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10433
                                                                    =
                                                                    let uu____10434
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10434] in
                                                                    let uu____10435
                                                                    =
                                                                    let uu____10446
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10446] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10433;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10435;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10471
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10471))
                                                                    | 
                                                                    uu____10474
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10475
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Generalize.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10495
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10495)) in
                                                                    match uu____10475
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
                                                                    let uu___1090_10514
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1090_10514.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1090_10514.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1090_10514.FStar_Syntax_Syntax.action_params);
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
                                  match uu____9050 with
                                  | (repr, return_repr, bind_repr, actions)
                                      ->
                                      let cl ts =
                                        let ts1 =
                                          FStar_Syntax_Subst.close_tscheme
                                            ed_bs ts in
                                        let ed_univs_closing =
                                          FStar_Syntax_Subst.univ_var_closing
                                            ed_univs in
                                        let uu____10557 =
                                          FStar_Syntax_Subst.shift_subst
                                            (FStar_List.length ed_bs)
                                            ed_univs_closing in
                                        FStar_Syntax_Subst.subst_tscheme
                                          uu____10557 ts1 in
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
                                            uu____10569 ->
                                            FStar_Syntax_Syntax.Primitive_eff
                                              combinators1
                                        | FStar_Syntax_Syntax.DM4F_eff
                                            uu____10570 ->
                                            FStar_Syntax_Syntax.DM4F_eff
                                              combinators1
                                        | uu____10571 ->
                                            failwith
                                              "Impossible! tc_eff_decl on a layered effect is not expected" in
                                      let ed3 =
                                        let uu___1110_10573 = ed2 in
                                        let uu____10574 = cl signature in
                                        let uu____10575 =
                                          FStar_List.map
                                            (fun a ->
                                               let uu___1113_10583 = a in
                                               let uu____10584 =
                                                 let uu____10585 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_defn)) in
                                                 FStar_All.pipe_right
                                                   uu____10585
                                                   FStar_Pervasives_Native.snd in
                                               let uu____10610 =
                                                 let uu____10611 =
                                                   cl
                                                     ((a.FStar_Syntax_Syntax.action_univs),
                                                       (a.FStar_Syntax_Syntax.action_typ)) in
                                                 FStar_All.pipe_right
                                                   uu____10611
                                                   FStar_Pervasives_Native.snd in
                                               {
                                                 FStar_Syntax_Syntax.action_name
                                                   =
                                                   (uu___1113_10583.FStar_Syntax_Syntax.action_name);
                                                 FStar_Syntax_Syntax.action_unqualified_name
                                                   =
                                                   (uu___1113_10583.FStar_Syntax_Syntax.action_unqualified_name);
                                                 FStar_Syntax_Syntax.action_univs
                                                   =
                                                   (uu___1113_10583.FStar_Syntax_Syntax.action_univs);
                                                 FStar_Syntax_Syntax.action_params
                                                   =
                                                   (uu___1113_10583.FStar_Syntax_Syntax.action_params);
                                                 FStar_Syntax_Syntax.action_defn
                                                   = uu____10584;
                                                 FStar_Syntax_Syntax.action_typ
                                                   = uu____10610
                                               }) actions in
                                        {
                                          FStar_Syntax_Syntax.mname =
                                            (uu___1110_10573.FStar_Syntax_Syntax.mname);
                                          FStar_Syntax_Syntax.cattributes =
                                            (uu___1110_10573.FStar_Syntax_Syntax.cattributes);
                                          FStar_Syntax_Syntax.univs =
                                            (uu___1110_10573.FStar_Syntax_Syntax.univs);
                                          FStar_Syntax_Syntax.binders =
                                            (uu___1110_10573.FStar_Syntax_Syntax.binders);
                                          FStar_Syntax_Syntax.signature =
                                            uu____10574;
                                          FStar_Syntax_Syntax.combinators =
                                            combinators2;
                                          FStar_Syntax_Syntax.actions =
                                            uu____10575;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            (uu___1110_10573.FStar_Syntax_Syntax.eff_attrs)
                                        } in
                                      ((let uu____10637 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env)
                                            (FStar_Options.Other "ED") in
                                        if uu____10637
                                        then
                                          let uu____10638 =
                                            FStar_Syntax_Print.eff_decl_to_string
                                              false ed3 in
                                          FStar_Util.print1
                                            "Typechecked effect declaration:\n\t%s\n"
                                            uu____10638
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
          let uu____10668 =
            let uu____10689 =
              FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
            if uu____10689
            then tc_layered_eff_decl
            else tc_non_layered_eff_decl in
          uu____10668 env ed quals attrs
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
        let fail uu____10739 =
          let uu____10740 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____10745 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____10740 uu____10745 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____10789)::(wp, uu____10791)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____10820 -> fail ())
        | uu____10821 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____10833 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____10833
       then
         let uu____10834 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____10834
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____10848 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____10848.FStar_Syntax_Syntax.pos in
       let uu____10857 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____10857 with
       | (us, lift, lift_ty) ->
           ((let uu____10868 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____10868
             then
               let uu____10869 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____10874 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____10869 uu____10874
             else ());
            (let uu____10880 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____10880 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____10895 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____10896 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____10897 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____10895 uu____10896 s uu____10897 in
                   let uu____10898 =
                     let uu____10905 =
                       let uu____10910 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____10910
                         (fun uu____10927 ->
                            match uu____10927 with
                            | (t, u) ->
                                let uu____10938 =
                                  let uu____10939 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____10939
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____10938, u)) in
                     match uu____10905 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____10957 =
                             let uu____10958 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____10958.FStar_Syntax_Syntax.n in
                           match uu____10957 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____10970)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____10997 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____10997 with
                                | (a', uu____11007)::bs1 ->
                                    let uu____11027 =
                                      let uu____11028 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____11028
                                        FStar_Pervasives_Native.fst in
                                    let uu____11093 =
                                      let uu____11106 =
                                        let uu____11109 =
                                          let uu____11110 =
                                            let uu____11117 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11117) in
                                          FStar_Syntax_Syntax.NT uu____11110 in
                                        [uu____11109] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11106 in
                                    FStar_All.pipe_right uu____11027
                                      uu____11093)
                           | uu____11132 ->
                               let uu____11133 =
                                 let uu____11138 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11138) in
                               FStar_Errors.raise_error uu____11133 r in
                         let uu____11147 =
                           let uu____11158 =
                             let uu____11163 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11170 =
                               let uu____11171 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11171
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11163 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11170 in
                           match uu____11158 with
                           | (f_sort, g) ->
                               let uu____11192 =
                                 let uu____11199 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11199
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11192, g) in
                         (match uu____11147 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11265 =
                                let uu____11270 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11271 =
                                  let uu____11272 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11272
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11270 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11271 in
                              (match uu____11265 with
                               | (repr, g_repr) ->
                                   let uu____11289 =
                                     let uu____11294 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11295 =
                                       let uu____11296 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11297 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11296 uu____11297 in
                                     pure_wp_uvar uu____11294 repr
                                       uu____11295 r in
                                   (match uu____11289 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11307 =
                                            let uu____11308 =
                                              let uu____11309 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11309] in
                                            let uu____11310 =
                                              let uu____11321 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11321] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11308;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11310;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11307 in
                                        let uu____11354 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11357 =
                                          let uu____11358 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11358 guard_wp in
                                        (uu____11354, uu____11357)))) in
                   match uu____10898 with
                   | (k, g_k) ->
                       ((let uu____11368 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11368
                         then
                           let uu____11369 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11369
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11375 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11375
                          then
                            let uu____11376 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11376
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          let check_non_informative_binders =
                            (FStar_TypeChecker_Env.is_reifiable_effect env
                               sub.FStar_Syntax_Syntax.target)
                              &&
                              (let uu____11381 =
                                 FStar_TypeChecker_Env.fv_with_lid_has_attr
                                   env sub.FStar_Syntax_Syntax.target
                                   FStar_Parser_Const.allow_informative_binders_attr in
                               Prims.op_Negation uu____11381) in
                          (let uu____11383 =
                             let uu____11384 = FStar_Syntax_Subst.compress k1 in
                             uu____11384.FStar_Syntax_Syntax.n in
                           match uu____11383 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11409 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11409 with
                                | (a::bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11440 =
                                      let uu____11459 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11459
                                        (fun uu____11534 ->
                                           match uu____11534 with
                                           | (l1, l2) ->
                                               let uu____11607 =
                                                 FStar_List.hd l2 in
                                               (l1, uu____11607)) in
                                    (match uu____11440 with
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
                             let uu___1223_11680 = sub in
                             let uu____11681 =
                               let uu____11684 =
                                 let uu____11685 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____11685) in
                               FStar_Pervasives_Native.Some uu____11684 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1223_11680.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1223_11680.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____11681;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____11699 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____11699
                            then
                              let uu____11700 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____11700
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
          let uu____11733 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Generalize.generalize_universes env1 uu____11733 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____11736 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____11736
        then tc_layered_lift env sub
        else
          (let uu____11738 =
             let uu____11745 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____11745 in
           match uu____11738 with
           | (a, wp_a_src) ->
               let uu____11752 =
                 let uu____11759 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____11759 in
               (match uu____11752 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____11767 =
                        let uu____11770 =
                          let uu____11771 =
                            let uu____11778 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____11778) in
                          FStar_Syntax_Syntax.NT uu____11771 in
                        [uu____11770] in
                      FStar_Syntax_Subst.subst uu____11767 wp_b_tgt in
                    let expected_k =
                      let uu____11786 =
                        let uu____11795 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____11802 =
                          let uu____11811 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____11811] in
                        uu____11795 :: uu____11802 in
                      let uu____11836 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____11786 uu____11836 in
                    let repr_type eff_name a1 wp =
                      (let uu____11858 =
                         let uu____11859 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____11859 in
                       if uu____11858
                       then
                         let uu____11860 =
                           let uu____11865 =
                             let uu____11866 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____11866 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____11865) in
                         let uu____11867 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____11860 uu____11867
                       else ());
                      (let uu____11869 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____11869 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____11901 =
                               let uu____11902 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____11902
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____11901 in
                           let uu____11909 =
                             let uu____11910 =
                               let uu____11927 =
                                 let uu____11938 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____11947 =
                                   let uu____11958 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____11958] in
                                 uu____11938 :: uu____11947 in
                               (repr, uu____11927) in
                             FStar_Syntax_Syntax.Tm_app uu____11910 in
                           let uu____12003 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____11909 uu____12003) in
                    let uu____12004 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12176 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12185 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12185 with
                              | (usubst, uvs1) ->
                                  let uu____12208 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12209 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12208, uu____12209)
                            else (env, lift_wp) in
                          (match uu____12176 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12254 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12254)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12325 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12338 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12338 with
                              | (usubst, uvs) ->
                                  let uu____12363 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12363)
                            else ([], lift) in
                          (match uu____12325 with
                           | (uvs, lift1) ->
                               ((let uu____12398 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12398
                                 then
                                   let uu____12399 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12399
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12402 =
                                   let uu____12409 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12409 lift1 in
                                 match uu____12402 with
                                 | (lift2, comp, uu____12434) ->
                                     let uu____12435 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12435 with
                                      | (uu____12464, lift_wp, lift_elab) ->
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
                                            let uu____12491 =
                                              let uu____12502 =
                                                FStar_TypeChecker_Generalize.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____12502 in
                                            let uu____12519 =
                                              FStar_TypeChecker_Generalize.generalize_universes
                                                env lift_wp1 in
                                            (uu____12491, uu____12519)
                                          else
                                            (let uu____12547 =
                                               let uu____12558 =
                                                 let uu____12567 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____12567) in
                                               FStar_Pervasives_Native.Some
                                                 uu____12558 in
                                             let uu____12582 =
                                               let uu____12591 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____12591) in
                                             (uu____12547, uu____12582)))))) in
                    (match uu____12004 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1307_12655 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1307_12655.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1307_12655.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1307_12655.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1307_12655.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1307_12655.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1307_12655.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1307_12655.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1307_12655.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1307_12655.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1307_12655.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1307_12655.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1307_12655.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1307_12655.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1307_12655.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1307_12655.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1307_12655.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1307_12655.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1307_12655.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1307_12655.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1307_12655.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1307_12655.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1307_12655.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1307_12655.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1307_12655.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1307_12655.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1307_12655.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1307_12655.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1307_12655.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1307_12655.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1307_12655.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1307_12655.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1307_12655.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1307_12655.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1307_12655.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1307_12655.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1307_12655.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1307_12655.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1307_12655.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1307_12655.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1307_12655.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1307_12655.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1307_12655.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1307_12655.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1307_12655.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1307_12655.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1307_12655.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____12687 =
                                 let uu____12692 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____12692 with
                                 | (usubst, uvs1) ->
                                     let uu____12715 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____12716 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____12715, uu____12716) in
                               (match uu____12687 with
                                | (env2, lift2) ->
                                    let uu____12721 =
                                      let uu____12728 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____12728 in
                                    (match uu____12721 with
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
                                             let uu____12754 =
                                               let uu____12755 =
                                                 let uu____12772 =
                                                   let uu____12783 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____12792 =
                                                     let uu____12803 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____12803] in
                                                   uu____12783 :: uu____12792 in
                                                 (lift_wp1, uu____12772) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____12755 in
                                             let uu____12848 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____12754 uu____12848 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____12852 =
                                             let uu____12861 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____12868 =
                                               let uu____12877 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____12884 =
                                                 let uu____12893 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____12893] in
                                               uu____12877 :: uu____12884 in
                                             uu____12861 :: uu____12868 in
                                           let uu____12924 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____12852 uu____12924 in
                                         let uu____12927 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____12927 with
                                          | (expected_k2, uu____12937,
                                             uu____12938) ->
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
                                                   let uu____12942 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____12942)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____12950 =
                             let uu____12951 =
                               let uu____12952 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____12952
                                 FStar_List.length in
                             uu____12951 <> Prims.int_one in
                           if uu____12950
                           then
                             let uu____12971 =
                               let uu____12976 =
                                 let uu____12977 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____12978 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____12979 =
                                   let uu____12980 =
                                     let uu____12981 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____12981
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____12980
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____12977 uu____12978 uu____12979 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____12976) in
                             FStar_Errors.raise_error uu____12971 r
                           else ());
                          (let uu____13002 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____13004 =
                                  let uu____13005 =
                                    let uu____13008 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____13008
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____13005
                                    FStar_List.length in
                                uu____13004 <> Prims.int_one) in
                           if uu____13002
                           then
                             let uu____13043 =
                               let uu____13048 =
                                 let uu____13049 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____13050 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____13051 =
                                   let uu____13052 =
                                     let uu____13053 =
                                       let uu____13056 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____13056
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____13053
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____13052
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____13049 uu____13050 uu____13051 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____13048) in
                             FStar_Errors.raise_error uu____13043 r
                           else ());
                          (let uu___1344_13092 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1344_13092.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1344_13092.FStar_Syntax_Syntax.target);
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
    fun uu____13122 ->
      fun r ->
        match uu____13122 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13145 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13169 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13169 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13200 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13200 c in
                     let uu____13209 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13209, uvs1, tps1, c1)) in
            (match uu____13145 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13229 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13229 with
                  | (tps2, c2) ->
                      let uu____13244 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13244 with
                       | (tps3, env3, us) ->
                           let uu____13262 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13262 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13288)::uu____13289 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13308 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13314 =
                                    let uu____13315 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13315 in
                                  if uu____13314
                                  then
                                    let uu____13316 =
                                      let uu____13321 =
                                        let uu____13322 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13323 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13322 uu____13323 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13321) in
                                    FStar_Errors.raise_error uu____13316 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13327 =
                                    let uu____13328 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Generalize.generalize_universes
                                      env0 uu____13328 in
                                  match uu____13327 with
                                  | (uvs2, t) ->
                                      let uu____13357 =
                                        let uu____13362 =
                                          let uu____13375 =
                                            let uu____13376 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13376.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13375) in
                                        match uu____13362 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13391, c5)) -> ([], c5)
                                        | (uu____13433,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____13472 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13357 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____13500 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____13500 with
                                               | (uu____13505, t1) ->
                                                   let uu____13507 =
                                                     let uu____13512 =
                                                       let uu____13513 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____13514 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____13515 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____13513
                                                         uu____13514
                                                         uu____13515 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____13512) in
                                                   FStar_Errors.raise_error
                                                     uu____13507 r)
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
              let uu____13551 =
                let uu____13552 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13552 FStar_Ident.string_of_id in
              let uu____13553 =
                let uu____13554 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13554 FStar_Ident.string_of_id in
              let uu____13555 =
                let uu____13556 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13556 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____13551 uu____13553
                uu____13555 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____13562 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____13562 with
            | (us, t, ty) ->
                let uu____13576 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____13576 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____13589 =
                         let uu____13594 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____13594
                           (fun uu____13611 ->
                              match uu____13611 with
                              | (t1, u) ->
                                  let uu____13622 =
                                    let uu____13623 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____13623
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____13622, u)) in
                       match uu____13589 with
                       | (a, u_a) ->
                           let uu____13630 =
                             let uu____13635 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____13635
                               (fun uu____13652 ->
                                  match uu____13652 with
                                  | (t1, u) ->
                                      let uu____13663 =
                                        let uu____13664 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____13664
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____13663, u)) in
                           (match uu____13630 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____13680 =
                                    let uu____13681 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____13681.FStar_Syntax_Syntax.n in
                                  match uu____13680 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____13693) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____13720 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____13720 with
                                       | (a', uu____13730)::(b', uu____13732)::bs1
                                           ->
                                           let uu____13762 =
                                             let uu____13763 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____13763
                                               FStar_Pervasives_Native.fst in
                                           let uu____13860 =
                                             let uu____13873 =
                                               let uu____13876 =
                                                 let uu____13877 =
                                                   let uu____13884 =
                                                     let uu____13887 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____13887
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____13884) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____13877 in
                                               let uu____13900 =
                                                 let uu____13903 =
                                                   let uu____13904 =
                                                     let uu____13911 =
                                                       let uu____13914 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____13914
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____13911) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____13904 in
                                                 [uu____13903] in
                                               uu____13876 :: uu____13900 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____13873 in
                                           FStar_All.pipe_right uu____13762
                                             uu____13860)
                                  | uu____13935 ->
                                      let uu____13936 =
                                        let uu____13941 =
                                          let uu____13942 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____13943 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____13942 uu____13943 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____13941) in
                                      FStar_Errors.raise_error uu____13936 r in
                                let bs = a :: b :: rest_bs in
                                let uu____13973 =
                                  let uu____13984 =
                                    let uu____13989 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____13990 =
                                      let uu____13991 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____13991
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____13989 r m u_a uu____13990 in
                                  match uu____13984 with
                                  | (repr, g) ->
                                      let uu____14012 =
                                        let uu____14019 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____14019
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____14012, g) in
                                (match uu____13973 with
                                 | (f, guard_f) ->
                                     let uu____14050 =
                                       let x_a =
                                         let uu____14068 =
                                           let uu____14069 =
                                             let uu____14070 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____14070
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____14069 in
                                         FStar_All.pipe_right uu____14068
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____14085 =
                                         let uu____14090 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____14109 =
                                           let uu____14110 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____14110
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____14090 r n u_b uu____14109 in
                                       match uu____14085 with
                                       | (repr, g) ->
                                           let uu____14131 =
                                             let uu____14138 =
                                               let uu____14139 =
                                                 let uu____14140 =
                                                   let uu____14143 =
                                                     let uu____14146 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14146 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14143 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14140 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14139 in
                                             FStar_All.pipe_right uu____14138
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____14131, g) in
                                     (match uu____14050 with
                                      | (g, guard_g) ->
                                          let uu____14189 =
                                            let uu____14194 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14195 =
                                              let uu____14196 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14196
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14194 r p u_b uu____14195 in
                                          (match uu____14189 with
                                           | (repr, guard_repr) ->
                                               let uu____14211 =
                                                 let uu____14216 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14217 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14216
                                                   repr uu____14217 r in
                                               (match uu____14211 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14227 =
                                                        let uu____14230 =
                                                          let uu____14231 =
                                                            let uu____14232 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14232] in
                                                          let uu____14233 =
                                                            let uu____14244 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14244] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14231;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14233;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14230 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14227 in
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
                                                     (let uu____14304 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14304
                                                      then
                                                        let uu____14305 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14310 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14305
                                                          uu____14310
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
                                                          (let uu____14319 =
                                                             FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                               env1 p
                                                               FStar_Parser_Const.allow_informative_binders_attr in
                                                           Prims.op_Negation
                                                             uu____14319) in
                                                      (let uu____14321 =
                                                         let uu____14322 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14322.FStar_Syntax_Syntax.n in
                                                       match uu____14321 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14347 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14347
                                                            with
                                                            | (a1::b1::bs2,
                                                               c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14391
                                                                  =
                                                                  let uu____14418
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____14418
                                                                    (
                                                                    fun
                                                                    uu____14502
                                                                    ->
                                                                    match uu____14502
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____14583
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____14610
                                                                    =
                                                                    let uu____14617
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____14617
                                                                    FStar_List.hd in
                                                                    (l1,
                                                                    uu____14583,
                                                                    uu____14610)) in
                                                                (match uu____14391
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____14732
                                                                    =
                                                                    let uu____14733
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____14733.FStar_Syntax_Syntax.n in
                                                                    match uu____14732
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____14738,
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
                                                      (let uu____14782 =
                                                         let uu____14787 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____14787) in
                                                       FStar_Errors.log_issue
                                                         r uu____14782);
                                                      (let uu____14788 =
                                                         let uu____14789 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____14789) in
                                                       ((us1, t),
                                                         uu____14788))))))))))))
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
            let uu____14836 =
              let uu____14837 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____14837 FStar_Ident.string_of_id in
            let uu____14838 =
              let uu____14839 =
                let uu____14840 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____14840 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____14839 in
            Prims.op_Hat uu____14836 uu____14838 in
          let uu____14841 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____14841 with
          | (us, t, ty) ->
              let uu____14855 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____14855 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____14868 =
                       let uu____14873 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____14873
                         (fun uu____14890 ->
                            match uu____14890 with
                            | (t1, u) ->
                                let uu____14901 =
                                  let uu____14902 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____14902
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____14901, u)) in
                     match uu____14868 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____14918 =
                             let uu____14919 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____14919.FStar_Syntax_Syntax.n in
                           match uu____14918 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____14931)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____14958 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____14958 with
                                | (a', uu____14968)::bs1 ->
                                    let uu____14988 =
                                      let uu____14989 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____14989
                                        FStar_Pervasives_Native.fst in
                                    let uu____15054 =
                                      let uu____15067 =
                                        let uu____15070 =
                                          let uu____15071 =
                                            let uu____15078 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____15078) in
                                          FStar_Syntax_Syntax.NT uu____15071 in
                                        [uu____15070] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____15067 in
                                    FStar_All.pipe_right uu____14988
                                      uu____15054)
                           | uu____15093 ->
                               let uu____15094 =
                                 let uu____15099 =
                                   let uu____15100 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____15101 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____15100 uu____15101 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____15099) in
                               FStar_Errors.raise_error uu____15094 r in
                         let bs = a :: rest_bs in
                         let uu____15125 =
                           let uu____15136 =
                             let uu____15141 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15142 =
                               let uu____15143 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15143
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15141 r m u uu____15142 in
                           match uu____15136 with
                           | (repr, g) ->
                               let uu____15164 =
                                 let uu____15171 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15171
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15164, g) in
                         (match uu____15125 with
                          | (f, guard_f) ->
                              let uu____15202 =
                                let uu____15207 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15208 =
                                  let uu____15209 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15209
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15207 r n u uu____15208 in
                              (match uu____15202 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15224 =
                                     let uu____15229 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15230 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15229 ret_t
                                       uu____15230 r in
                                   (match uu____15224 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15238 =
                                            let uu____15239 =
                                              let uu____15240 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15240] in
                                            let uu____15241 =
                                              let uu____15252 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15252] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15239;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15241;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15238 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15307 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15307
                                          then
                                            let uu____15308 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15308
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
                                             let uu____15315 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15315
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15319 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15319
                                            then
                                              let uu____15320 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15320
                                            else ());
                                           (let check_non_informative_binders
                                              =
                                              (FStar_TypeChecker_Env.is_reifiable_effect
                                                 env n)
                                                &&
                                                (let uu____15328 =
                                                   FStar_TypeChecker_Env.fv_with_lid_has_attr
                                                     env n
                                                     FStar_Parser_Const.allow_informative_binders_attr in
                                                 Prims.op_Negation
                                                   uu____15328) in
                                            (let uu____15330 =
                                               let uu____15331 =
                                                 FStar_Syntax_Subst.compress
                                                   k1 in
                                               uu____15331.FStar_Syntax_Syntax.n in
                                             match uu____15330 with
                                             | FStar_Syntax_Syntax.Tm_arrow
                                                 (bs1, c1) ->
                                                 let uu____15356 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs1 c1 in
                                                 (match uu____15356 with
                                                  | (a1::bs2, c2) ->
                                                      let res_t =
                                                        FStar_Syntax_Util.comp_result
                                                          c2 in
                                                      let uu____15387 =
                                                        let uu____15406 =
                                                          FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs2)
                                                               -
                                                               Prims.int_one)
                                                            bs2 in
                                                        FStar_All.pipe_right
                                                          uu____15406
                                                          (fun uu____15481 ->
                                                             match uu____15481
                                                             with
                                                             | (l1, l2) ->
                                                                 let uu____15554
                                                                   =
                                                                   FStar_List.hd
                                                                    l2 in
                                                                 (l1,
                                                                   uu____15554)) in
                                                      (match uu____15387 with
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
                                            (let uu____15627 =
                                               let uu____15632 =
                                                 FStar_Util.format1
                                                   "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                   combinator_name in
                                               (FStar_Errors.Warning_BleedingEdge_Feature,
                                                 uu____15632) in
                                             FStar_Errors.log_issue r
                                               uu____15627);
                                            (let uu____15633 =
                                               let uu____15634 =
                                                 FStar_All.pipe_right k1
                                                   (FStar_Syntax_Subst.close_univ_vars
                                                      us1) in
                                               (us1, uu____15634) in
                                             ((us1, t), uu____15633))))))))))))