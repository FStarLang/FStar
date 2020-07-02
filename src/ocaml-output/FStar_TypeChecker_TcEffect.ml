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
      FStar_Syntax_Syntax.term Prims.list -> FStar_Range.range -> unit)
  =
  fun env ->
    fun bs ->
      fun repr_terms ->
        fun r ->
          let repr_args repr =
            let uu____394 =
              let uu____395 = FStar_Syntax_Subst.compress repr in
              uu____395.FStar_Syntax_Syntax.n in
            match uu____394 with
            | FStar_Syntax_Syntax.Tm_app (uu____408, args) -> args
            | FStar_Syntax_Syntax.Tm_arrow (uu____434::[], c) ->
                FStar_All.pipe_right c FStar_Syntax_Util.comp_effect_args
            | uu____476 ->
                let uu____477 =
                  let uu____483 =
                    let uu____485 = FStar_Syntax_Print.term_to_string repr in
                    FStar_Util.format1
                      "Unexpected repr term %s when validating layered effect combinator binders"
                      uu____485 in
                  (FStar_Errors.Fatal_UnexpectedEffect, uu____483) in
                FStar_Errors.raise_error uu____477 r in
          let rec head_names_in_term arg =
            let uu____509 =
              let uu____510 = FStar_Syntax_Subst.compress arg in
              uu____510.FStar_Syntax_Syntax.n in
            match uu____509 with
            | FStar_Syntax_Syntax.Tm_name uu____517 -> [arg]
            | FStar_Syntax_Syntax.Tm_app (head, uu____523) ->
                let uu____548 =
                  let uu____549 = FStar_Syntax_Subst.compress head in
                  uu____549.FStar_Syntax_Syntax.n in
                (match uu____548 with
                 | FStar_Syntax_Syntax.Tm_name uu____556 -> [head]
                 | uu____561 -> [])
            | FStar_Syntax_Syntax.Tm_abs (uu____564, body, uu____566) ->
                head_names_in_term body
            | uu____591 -> [] in
          let head_names_in_args args =
            let uu____620 =
              FStar_All.pipe_right args
                (FStar_List.map FStar_Pervasives_Native.fst) in
            FStar_All.pipe_right uu____620
              (FStar_List.collect head_names_in_term) in
          let repr_names_args =
            FStar_List.collect
              (fun repr ->
                 let uu____659 = FStar_All.pipe_right repr repr_args in
                 FStar_All.pipe_right uu____659 head_names_in_args)
              repr_terms in
          (let uu____689 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
               (FStar_Options.Other "LayeredEffectsTc") in
           if uu____689
           then
             let uu____694 =
               FStar_List.fold_left
                 (fun s ->
                    fun t ->
                      let uu____703 =
                        let uu____705 = FStar_Syntax_Print.term_to_string t in
                        Prims.op_Hat "; " uu____705 in
                      Prims.op_Hat s uu____703) "" repr_names_args in
             let uu____709 = FStar_Syntax_Print.binders_to_string "; " bs in
             FStar_Util.print2
               "Checking layered effect combinator binders validity, names: %s, binders: %s\n\n"
               uu____694 uu____709
           else ());
          (let valid_binder b =
             (FStar_List.existsb
                (fun t ->
                   let uu____737 =
                     let uu____738 =
                       let uu____739 =
                         FStar_All.pipe_right b FStar_Pervasives_Native.fst in
                       FStar_All.pipe_right uu____739
                         FStar_Syntax_Syntax.bv_to_name in
                     FStar_Syntax_Util.eq_tm uu____738 t in
                   uu____737 = FStar_Syntax_Util.Equal) repr_names_args)
               ||
               (match FStar_Pervasives_Native.snd b with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                    (FStar_Syntax_Syntax.Arg_qualifier_meta_attr uu____752))
                    -> true
                | uu____756 -> false) in
           let invalid_binders =
             FStar_List.filter (fun b -> Prims.op_Negation (valid_binder b))
               bs in
           if (FStar_List.length invalid_binders) <> Prims.int_zero
           then
             let uu____792 =
               let uu____798 =
                 let uu____800 =
                   FStar_Syntax_Print.binders_to_string "; " invalid_binders in
                 FStar_Util.format1
                   "Binders %s neither appear as repr indices nor have an associated tactic"
                   uu____800 in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____798) in
             FStar_Errors.raise_error uu____792 r
           else ())
let (tc_layered_eff_decl :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.eff_decl)
  =
  fun env0 ->
    fun ed ->
      fun quals ->
        (let uu____828 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffectsTc") in
         if uu____828
         then
           let uu____833 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____833
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____851 =
             let uu____857 =
               let uu____859 =
                 let uu____861 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 Prims.op_Hat uu____861 ")" in
               Prims.op_Hat "Binders are not supported for layered effects ("
                 uu____859 in
             (FStar_Errors.Fatal_UnexpectedEffect, uu____857) in
           let uu____866 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname in
           FStar_Errors.raise_error uu____851 uu____866)
        else ();
        (let log_combinator s uu____892 =
           match uu____892 with
           | (us, t, ty) ->
               let uu____921 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffectsTc") in
               if uu____921
               then
                 let uu____926 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____928 = FStar_Syntax_Print.tscheme_to_string (us, t) in
                 let uu____934 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty) in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n" uu____926 s
                   uu____928 uu____934
               else () in
         let fresh_a_and_u_a a =
           let uu____959 = FStar_Syntax_Util.type_u () in
           FStar_All.pipe_right uu____959
             (fun uu____976 ->
                match uu____976 with
                | (t, u) ->
                    let uu____987 =
                      let uu____988 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t in
                      FStar_All.pipe_right uu____988
                        FStar_Syntax_Syntax.mk_binder in
                    (uu____987, u)) in
         let fresh_x_a x a =
           let uu____1002 =
             let uu____1003 =
               let uu____1004 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst in
               FStar_All.pipe_right uu____1004 FStar_Syntax_Syntax.bv_to_name in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____1003 in
           FStar_All.pipe_right uu____1002 FStar_Syntax_Syntax.mk_binder in
         let check_and_gen1 =
           let uu____1038 =
             FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
           check_and_gen env0 uu____1038 in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
           let uu____1058 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature in
           match uu____1058 with
           | (sig_us, sig_t, sig_ty) ->
               let uu____1082 =
                 FStar_Syntax_Subst.open_univ_vars sig_us sig_t in
               (match uu____1082 with
                | (us, t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                    let uu____1102 = fresh_a_and_u_a "a" in
                    (match uu____1102 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____1123 =
                             let uu____1124 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst in
                             FStar_All.pipe_right uu____1124
                               FStar_Syntax_Syntax.bv_to_name in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____1123 in
                         let bs = a :: rest_bs in
                         let k =
                           let uu____1155 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff in
                           FStar_Syntax_Util.arrow bs uu____1155 in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____1160 =
                             let uu____1163 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env) in
                             FStar_Syntax_Subst.close_univ_vars us uu____1163 in
                           (sig_us, uu____1160, sig_ty))))) in
         log_combinator "signature" signature;
         (let repr =
            let repr_ts =
              let uu____1190 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr in
              FStar_All.pipe_right uu____1190 FStar_Util.must in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos in
            let uu____1202 = check_and_gen1 "repr" Prims.int_one repr_ts in
            match uu____1202 with
            | (repr_us, repr_t, repr_ty) ->
                let uu____1226 =
                  FStar_Syntax_Subst.open_univ_vars repr_us repr_ty in
                (match uu____1226 with
                 | (us, ty) ->
                     let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                     let uu____1246 = fresh_a_and_u_a "a" in
                     (match uu____1246 with
                      | (a, u) ->
                          let rest_bs =
                            let signature_ts =
                              let uu____1268 = signature in
                              match uu____1268 with
                              | (us1, t, uu____1283) -> (us1, t) in
                            let uu____1300 =
                              let uu____1301 =
                                FStar_All.pipe_right a
                                  FStar_Pervasives_Native.fst in
                              FStar_All.pipe_right uu____1301
                                FStar_Syntax_Syntax.bv_to_name in
                            FStar_TypeChecker_Util.layered_effect_indices_as_binders
                              env r ed.FStar_Syntax_Syntax.mname signature_ts
                              u uu____1300 in
                          let bs = a :: rest_bs in
                          let k =
                            let uu____1328 =
                              let uu____1331 = FStar_Syntax_Util.type_u () in
                              FStar_All.pipe_right uu____1331
                                (fun uu____1344 ->
                                   match uu____1344 with
                                   | (t, u1) ->
                                       let uu____1351 =
                                         let uu____1354 =
                                           FStar_TypeChecker_Env.new_u_univ
                                             () in
                                         FStar_Pervasives_Native.Some
                                           uu____1354 in
                                       FStar_Syntax_Syntax.mk_Total' t
                                         uu____1351) in
                            FStar_Syntax_Util.arrow bs uu____1328 in
                          let g = FStar_TypeChecker_Rel.teq env ty k in
                          (FStar_TypeChecker_Rel.force_trivial_guard env g;
                           (let uu____1357 =
                              let uu____1360 =
                                FStar_All.pipe_right k
                                  (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                     env) in
                              FStar_Syntax_Subst.close_univ_vars us
                                uu____1360 in
                            (repr_us, repr_t, uu____1357))))) in
          log_combinator "repr" repr;
          (let fresh_repr r env u a_tm =
             let signature_ts =
               let uu____1395 = signature in
               match uu____1395 with | (us, t, uu____1410) -> (us, t) in
             let repr_ts =
               let uu____1428 = repr in
               match uu____1428 with | (us, t, uu____1443) -> (us, t) in
             FStar_TypeChecker_Util.fresh_effect_repr env r
               ed.FStar_Syntax_Syntax.mname signature_ts
               (FStar_Pervasives_Native.Some repr_ts) u a_tm in
           let not_an_arrow_error comb n t r =
             let uu____1493 =
               let uu____1499 =
                 let uu____1501 =
                   FStar_Ident.string_of_lid ed.FStar_Syntax_Syntax.mname in
                 let uu____1503 = FStar_Util.string_of_int n in
                 let uu____1505 = FStar_Syntax_Print.tag_of_term t in
                 let uu____1507 = FStar_Syntax_Print.term_to_string t in
                 FStar_Util.format5
                   "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                   uu____1501 comb uu____1503 uu____1505 uu____1507 in
               (FStar_Errors.Fatal_UnexpectedEffect, uu____1499) in
             FStar_Errors.raise_error uu____1493 r in
           let return_repr =
             let return_repr_ts =
               let uu____1537 =
                 FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
               FStar_All.pipe_right uu____1537 FStar_Util.must in
             let r =
               (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos in
             let uu____1549 =
               check_and_gen1 "return_repr" Prims.int_one return_repr_ts in
             match uu____1549 with
             | (ret_us, ret_t, ret_ty) ->
                 let uu____1573 =
                   FStar_Syntax_Subst.open_univ_vars ret_us ret_ty in
                 (match uu____1573 with
                  | (us, ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                      (check_no_subtyping_for_layered_combinator env ty
                         FStar_Pervasives_Native.None;
                       (let uu____1594 = fresh_a_and_u_a "a" in
                        match uu____1594 with
                        | (a, u_a) ->
                            let x_a = fresh_x_a "x" a in
                            let rest_bs =
                              let uu____1625 =
                                let uu____1626 =
                                  FStar_Syntax_Subst.compress ty in
                                uu____1626.FStar_Syntax_Syntax.n in
                              match uu____1625 with
                              | FStar_Syntax_Syntax.Tm_arrow (bs, uu____1638)
                                  when
                                  (FStar_List.length bs) >=
                                    (Prims.of_int (2))
                                  ->
                                  let uu____1666 =
                                    FStar_Syntax_Subst.open_binders bs in
                                  (match uu____1666 with
                                   | (a', uu____1676)::(x', uu____1678)::bs1
                                       ->
                                       let uu____1708 =
                                         let uu____1709 =
                                           let uu____1714 =
                                             let uu____1717 =
                                               let uu____1718 =
                                                 let uu____1725 =
                                                   FStar_Syntax_Syntax.bv_to_name
                                                     (FStar_Pervasives_Native.fst
                                                        a) in
                                                 (a', uu____1725) in
                                               FStar_Syntax_Syntax.NT
                                                 uu____1718 in
                                             [uu____1717] in
                                           FStar_Syntax_Subst.subst_binders
                                             uu____1714 in
                                         FStar_All.pipe_right bs1 uu____1709 in
                                       let uu____1732 =
                                         let uu____1745 =
                                           let uu____1748 =
                                             let uu____1749 =
                                               let uu____1756 =
                                                 FStar_Syntax_Syntax.bv_to_name
                                                   (FStar_Pervasives_Native.fst
                                                      x_a) in
                                               (x', uu____1756) in
                                             FStar_Syntax_Syntax.NT
                                               uu____1749 in
                                           [uu____1748] in
                                         FStar_Syntax_Subst.subst_binders
                                           uu____1745 in
                                       FStar_All.pipe_right uu____1708
                                         uu____1732)
                              | uu____1771 ->
                                  not_an_arrow_error "return"
                                    (Prims.of_int (2)) ty r in
                            let bs = a :: x_a :: rest_bs in
                            let uu____1795 =
                              let uu____1800 =
                                FStar_TypeChecker_Env.push_binders env bs in
                              let uu____1801 =
                                FStar_All.pipe_right
                                  (FStar_Pervasives_Native.fst a)
                                  FStar_Syntax_Syntax.bv_to_name in
                              fresh_repr r uu____1800 u_a uu____1801 in
                            (match uu____1795 with
                             | (repr1, g) ->
                                 let k =
                                   let uu____1821 =
                                     FStar_Syntax_Syntax.mk_Total' repr1
                                       (FStar_Pervasives_Native.Some u_a) in
                                   FStar_Syntax_Util.arrow bs uu____1821 in
                                 let g_eq =
                                   FStar_TypeChecker_Rel.teq env ty k in
                                 ((let uu____1826 =
                                     FStar_TypeChecker_Env.conj_guard g g_eq in
                                   FStar_TypeChecker_Rel.force_trivial_guard
                                     env uu____1826);
                                  (let k1 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env) in
                                   (let uu____1829 =
                                      let uu____1830 =
                                        FStar_Syntax_Subst.compress k1 in
                                      uu____1830.FStar_Syntax_Syntax.n in
                                    match uu____1829 with
                                    | FStar_Syntax_Syntax.Tm_arrow (bs1, c)
                                        ->
                                        let uu____1855 =
                                          FStar_Syntax_Subst.open_comp bs1 c in
                                        (match uu____1855 with
                                         | (bs2, c1) ->
                                             let res_t =
                                               FStar_Syntax_Util.comp_result
                                                 c1 in
                                             let bs3 =
                                               let uu____1866 =
                                                 FStar_List.splitAt
                                                   (Prims.of_int (2)) bs2 in
                                               FStar_All.pipe_right
                                                 uu____1866
                                                 FStar_Pervasives_Native.snd in
                                             validate_layered_effect_binders
                                               env bs3 [res_t] r));
                                   (let uu____1930 =
                                      FStar_All.pipe_right k1
                                        (FStar_Syntax_Subst.close_univ_vars
                                           us) in
                                    (ret_us, ret_t, uu____1930)))))))) in
           log_combinator "return_repr" return_repr;
           (let bind_repr =
              let bind_repr_ts =
                let uu____1961 =
                  FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                FStar_All.pipe_right uu____1961 FStar_Util.must in
              let r =
                (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos in
              let uu____1989 =
                check_and_gen1 "bind_repr" (Prims.of_int (2)) bind_repr_ts in
              match uu____1989 with
              | (bind_us, bind_t, bind_ty) ->
                  let uu____2013 =
                    FStar_Syntax_Subst.open_univ_vars bind_us bind_ty in
                  (match uu____2013 with
                   | (us, ty) ->
                       let env = FStar_TypeChecker_Env.push_univ_vars env0 us in
                       (check_no_subtyping_for_layered_combinator env ty
                          FStar_Pervasives_Native.None;
                        (let uu____2034 = fresh_a_and_u_a "a" in
                         match uu____2034 with
                         | (a, u_a) ->
                             let uu____2054 = fresh_a_and_u_a "b" in
                             (match uu____2054 with
                              | (b, u_b) ->
                                  let rest_bs =
                                    let uu____2083 =
                                      let uu____2084 =
                                        FStar_Syntax_Subst.compress ty in
                                      uu____2084.FStar_Syntax_Syntax.n in
                                    match uu____2083 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____2096) when
                                        (FStar_List.length bs) >=
                                          (Prims.of_int (4))
                                        ->
                                        let uu____2124 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        (match uu____2124 with
                                         | (a', uu____2134)::(b', uu____2136)::bs1
                                             ->
                                             let uu____2166 =
                                               let uu____2167 =
                                                 FStar_All.pipe_right bs1
                                                   (FStar_List.splitAt
                                                      ((FStar_List.length bs1)
                                                         - (Prims.of_int (2)))) in
                                               FStar_All.pipe_right
                                                 uu____2167
                                                 FStar_Pervasives_Native.fst in
                                             let uu____2233 =
                                               let uu____2246 =
                                                 let uu____2249 =
                                                   let uu____2250 =
                                                     let uu____2257 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a) in
                                                     (a', uu____2257) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____2250 in
                                                 let uu____2264 =
                                                   let uu____2267 =
                                                     let uu____2268 =
                                                       let uu____2275 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              b) in
                                                       (b', uu____2275) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2268 in
                                                   [uu____2267] in
                                                 uu____2249 :: uu____2264 in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____2246 in
                                             FStar_All.pipe_right uu____2166
                                               uu____2233)
                                    | uu____2290 ->
                                        not_an_arrow_error "bind"
                                          (Prims.of_int (4)) ty r in
                                  let bs = a :: b :: rest_bs in
                                  let uu____2314 =
                                    let uu____2325 =
                                      let uu____2330 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____2331 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____2330 u_a uu____2331 in
                                    match uu____2325 with
                                    | (repr1, g) ->
                                        let uu____2346 =
                                          let uu____2353 =
                                            FStar_Syntax_Syntax.gen_bv "f"
                                              FStar_Pervasives_Native.None
                                              repr1 in
                                          FStar_All.pipe_right uu____2353
                                            FStar_Syntax_Syntax.mk_binder in
                                        (uu____2346, g) in
                                  (match uu____2314 with
                                   | (f, guard_f) ->
                                       let uu____2393 =
                                         let x_a = fresh_x_a "x" a in
                                         let uu____2406 =
                                           let uu____2411 =
                                             FStar_TypeChecker_Env.push_binders
                                               env
                                               (FStar_List.append bs [x_a]) in
                                           let uu____2430 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst b)
                                               FStar_Syntax_Syntax.bv_to_name in
                                           fresh_repr r uu____2411 u_b
                                             uu____2430 in
                                         match uu____2406 with
                                         | (repr1, g) ->
                                             let uu____2445 =
                                               let uu____2452 =
                                                 let uu____2453 =
                                                   let uu____2454 =
                                                     let uu____2457 =
                                                       let uu____2460 =
                                                         FStar_TypeChecker_Env.new_u_univ
                                                           () in
                                                       FStar_Pervasives_Native.Some
                                                         uu____2460 in
                                                     FStar_Syntax_Syntax.mk_Total'
                                                       repr1 uu____2457 in
                                                   FStar_Syntax_Util.arrow
                                                     [x_a] uu____2454 in
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "g"
                                                   FStar_Pervasives_Native.None
                                                   uu____2453 in
                                               FStar_All.pipe_right
                                                 uu____2452
                                                 FStar_Syntax_Syntax.mk_binder in
                                             (uu____2445, g) in
                                       (match uu____2393 with
                                        | (g, guard_g) ->
                                            let uu____2512 =
                                              let uu____2517 =
                                                FStar_TypeChecker_Env.push_binders
                                                  env bs in
                                              let uu____2518 =
                                                FStar_All.pipe_right
                                                  (FStar_Pervasives_Native.fst
                                                     b)
                                                  FStar_Syntax_Syntax.bv_to_name in
                                              fresh_repr r uu____2517 u_b
                                                uu____2518 in
                                            (match uu____2512 with
                                             | (repr1, guard_repr) ->
                                                 let uu____2535 =
                                                   let uu____2540 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs in
                                                   let uu____2541 =
                                                     let uu____2543 =
                                                       FStar_Ident.string_of_lid
                                                         ed.FStar_Syntax_Syntax.mname in
                                                     FStar_Util.format1
                                                       "implicit for pure_wp in checking bind for %s"
                                                       uu____2543 in
                                                   pure_wp_uvar uu____2540
                                                     repr1 uu____2541 r in
                                                 (match uu____2535 with
                                                  | (pure_wp_uvar1,
                                                     g_pure_wp_uvar) ->
                                                      let k =
                                                        let uu____2563 =
                                                          let uu____2566 =
                                                            let uu____2567 =
                                                              let uu____2568
                                                                =
                                                                FStar_TypeChecker_Env.new_u_univ
                                                                  () in
                                                              [uu____2568] in
                                                            let uu____2569 =
                                                              let uu____2580
                                                                =
                                                                FStar_All.pipe_right
                                                                  pure_wp_uvar1
                                                                  FStar_Syntax_Syntax.as_arg in
                                                              [uu____2580] in
                                                            {
                                                              FStar_Syntax_Syntax.comp_univs
                                                                = uu____2567;
                                                              FStar_Syntax_Syntax.effect_name
                                                                =
                                                                FStar_Parser_Const.effect_PURE_lid;
                                                              FStar_Syntax_Syntax.result_typ
                                                                = repr1;
                                                              FStar_Syntax_Syntax.effect_args
                                                                = uu____2569;
                                                              FStar_Syntax_Syntax.flags
                                                                = []
                                                            } in
                                                          FStar_Syntax_Syntax.mk_Comp
                                                            uu____2566 in
                                                        FStar_Syntax_Util.arrow
                                                          (FStar_List.append
                                                             bs [f; g])
                                                          uu____2563 in
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
                                                        (let uu____2641 =
                                                           let uu____2642 =
                                                             FStar_Syntax_Subst.compress
                                                               k1 in
                                                           uu____2642.FStar_Syntax_Syntax.n in
                                                         match uu____2641
                                                         with
                                                         | FStar_Syntax_Syntax.Tm_arrow
                                                             (bs1, c) ->
                                                             let uu____2667 =
                                                               FStar_Syntax_Subst.open_comp
                                                                 bs1 c in
                                                             (match uu____2667
                                                              with
                                                              | (bs2, c1) ->
                                                                  let res_t =
                                                                    FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                  let uu____2677
                                                                    =
                                                                    let uu____2704
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                    FStar_All.pipe_right
                                                                    uu____2704
                                                                    (fun
                                                                    uu____2790
                                                                    ->
                                                                    match uu____2790
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____2871
                                                                    =
                                                                    let uu____2880
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l1
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____2880
                                                                    FStar_List.tl in
                                                                    let uu____2933
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____2960
                                                                    =
                                                                    let uu____2967
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____2967
                                                                    FStar_List.hd in
                                                                    (uu____2871,
                                                                    uu____2933,
                                                                    uu____2960)) in
                                                                  (match uu____2677
                                                                   with
                                                                   | 
                                                                   (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____3082
                                                                    =
                                                                    let uu____3083
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____3083.FStar_Syntax_Syntax.n in
                                                                    match uu____3082
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____3088,
                                                                    c2) ->
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    validate_layered_effect_binders
                                                                    env bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    g_sort;
                                                                    res_t] r)));
                                                        (let uu____3112 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                bind_us) in
                                                         (bind_us, bind_t,
                                                           uu____3112)))))))))))) in
            log_combinator "bind_repr" bind_repr;
            (let stronger_repr =
               let stronger_repr =
                 let ts =
                   let uu____3152 =
                     FStar_All.pipe_right ed
                       FStar_Syntax_Util.get_stronger_repr in
                   FStar_All.pipe_right uu____3152 FStar_Util.must in
                 let uu____3189 =
                   let uu____3190 =
                     let uu____3193 =
                       FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                     FStar_All.pipe_right uu____3193
                       FStar_Syntax_Subst.compress in
                   uu____3190.FStar_Syntax_Syntax.n in
                 match uu____3189 with
                 | FStar_Syntax_Syntax.Tm_unknown ->
                     let signature_ts =
                       let uu____3211 = signature in
                       match uu____3211 with | (us, t, uu____3226) -> (us, t) in
                     let uu____3243 =
                       FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                         [FStar_Syntax_Syntax.U_unknown] in
                     (match uu____3243 with
                      | (uu____3254, signature_t) ->
                          let uu____3256 =
                            let uu____3257 =
                              FStar_Syntax_Subst.compress signature_t in
                            uu____3257.FStar_Syntax_Syntax.n in
                          (match uu____3256 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____3267) ->
                               let bs1 = FStar_Syntax_Subst.open_binders bs in
                               let repr_t =
                                 let repr_ts =
                                   let uu____3293 = repr in
                                   match uu____3293 with
                                   | (us, t, uu____3308) -> (us, t) in
                                 let uu____3325 =
                                   FStar_TypeChecker_Env.inst_tscheme_with
                                     repr_ts [FStar_Syntax_Syntax.U_unknown] in
                                 FStar_All.pipe_right uu____3325
                                   FStar_Pervasives_Native.snd in
                               let repr_t_applied =
                                 let uu____3345 =
                                   let uu____3346 =
                                     let uu____3363 =
                                       let uu____3374 =
                                         let uu____3377 =
                                           FStar_All.pipe_right bs1
                                             (FStar_List.map
                                                FStar_Pervasives_Native.fst) in
                                         FStar_All.pipe_right uu____3377
                                           (FStar_List.map
                                              FStar_Syntax_Syntax.bv_to_name) in
                                       FStar_All.pipe_right uu____3374
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.as_arg) in
                                     (repr_t, uu____3363) in
                                   FStar_Syntax_Syntax.Tm_app uu____3346 in
                                 FStar_Syntax_Syntax.mk uu____3345
                                   FStar_Range.dummyRange in
                               let f_b =
                                 FStar_Syntax_Syntax.null_binder
                                   repr_t_applied in
                               let uu____3427 =
                                 let uu____3430 =
                                   let uu____3433 =
                                     FStar_All.pipe_right f_b
                                       FStar_Pervasives_Native.fst in
                                   FStar_All.pipe_right uu____3433
                                     FStar_Syntax_Syntax.bv_to_name in
                                 FStar_Syntax_Util.abs
                                   (FStar_List.append bs1 [f_b]) uu____3430
                                   FStar_Pervasives_Native.None in
                               ([], uu____3427)
                           | uu____3464 -> failwith "Impossible!"))
                 | uu____3472 -> ts in
               let r =
                 (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos in
               let uu____3476 =
                 check_and_gen1 "stronger_repr" Prims.int_one stronger_repr in
               match uu____3476 with
               | (stronger_us, stronger_t, stronger_ty) ->
                   ((let uu____3501 =
                       FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                         (FStar_Options.Other "LayeredEffectsTc") in
                     if uu____3501
                     then
                       let uu____3506 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_t) in
                       let uu____3512 =
                         FStar_Syntax_Print.tscheme_to_string
                           (stronger_us, stronger_ty) in
                       FStar_Util.print2
                         "stronger combinator typechecked with term: %s and type: %s\n"
                         uu____3506 uu____3512
                     else ());
                    (let uu____3521 =
                       FStar_Syntax_Subst.open_univ_vars stronger_us
                         stronger_ty in
                     match uu____3521 with
                     | (us, ty) ->
                         let env =
                           FStar_TypeChecker_Env.push_univ_vars env0 us in
                         (check_no_subtyping_for_layered_combinator env ty
                            FStar_Pervasives_Native.None;
                          (let uu____3542 = fresh_a_and_u_a "a" in
                           match uu____3542 with
                           | (a, u) ->
                               let rest_bs =
                                 let uu____3571 =
                                   let uu____3572 =
                                     FStar_Syntax_Subst.compress ty in
                                   uu____3572.FStar_Syntax_Syntax.n in
                                 match uu____3571 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs, uu____3584) when
                                     (FStar_List.length bs) >=
                                       (Prims.of_int (2))
                                     ->
                                     let uu____3612 =
                                       FStar_Syntax_Subst.open_binders bs in
                                     (match uu____3612 with
                                      | (a', uu____3622)::bs1 ->
                                          let uu____3642 =
                                            let uu____3643 =
                                              FStar_All.pipe_right bs1
                                                (FStar_List.splitAt
                                                   ((FStar_List.length bs1) -
                                                      Prims.int_one)) in
                                            FStar_All.pipe_right uu____3643
                                              FStar_Pervasives_Native.fst in
                                          let uu____3741 =
                                            let uu____3754 =
                                              let uu____3757 =
                                                let uu____3758 =
                                                  let uu____3765 =
                                                    FStar_Syntax_Syntax.bv_to_name
                                                      (FStar_Pervasives_Native.fst
                                                         a) in
                                                  (a', uu____3765) in
                                                FStar_Syntax_Syntax.NT
                                                  uu____3758 in
                                              [uu____3757] in
                                            FStar_Syntax_Subst.subst_binders
                                              uu____3754 in
                                          FStar_All.pipe_right uu____3642
                                            uu____3741)
                                 | uu____3780 ->
                                     not_an_arrow_error "stronger"
                                       (Prims.of_int (2)) ty r in
                               let bs = a :: rest_bs in
                               let uu____3798 =
                                 let uu____3809 =
                                   let uu____3814 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs in
                                   let uu____3815 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name in
                                   fresh_repr r uu____3814 u uu____3815 in
                                 match uu____3809 with
                                 | (repr1, g) ->
                                     let uu____3830 =
                                       let uu____3837 =
                                         FStar_Syntax_Syntax.gen_bv "f"
                                           FStar_Pervasives_Native.None repr1 in
                                       FStar_All.pipe_right uu____3837
                                         FStar_Syntax_Syntax.mk_binder in
                                     (uu____3830, g) in
                               (match uu____3798 with
                                | (f, guard_f) ->
                                    let uu____3877 =
                                      let uu____3882 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs in
                                      let uu____3883 =
                                        FStar_All.pipe_right
                                          (FStar_Pervasives_Native.fst a)
                                          FStar_Syntax_Syntax.bv_to_name in
                                      fresh_repr r uu____3882 u uu____3883 in
                                    (match uu____3877 with
                                     | (ret_t, guard_ret_t) ->
                                         let uu____3900 =
                                           let uu____3905 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs in
                                           let uu____3906 =
                                             let uu____3908 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             FStar_Util.format1
                                               "implicit for pure_wp in checking stronger for %s"
                                               uu____3908 in
                                           pure_wp_uvar uu____3905 ret_t
                                             uu____3906 r in
                                         (match uu____3900 with
                                          | (pure_wp_uvar1, guard_wp) ->
                                              let c =
                                                let uu____3926 =
                                                  let uu____3927 =
                                                    let uu____3928 =
                                                      FStar_TypeChecker_Env.new_u_univ
                                                        () in
                                                    [uu____3928] in
                                                  let uu____3929 =
                                                    let uu____3940 =
                                                      FStar_All.pipe_right
                                                        pure_wp_uvar1
                                                        FStar_Syntax_Syntax.as_arg in
                                                    [uu____3940] in
                                                  {
                                                    FStar_Syntax_Syntax.comp_univs
                                                      = uu____3927;
                                                    FStar_Syntax_Syntax.effect_name
                                                      =
                                                      FStar_Parser_Const.effect_PURE_lid;
                                                    FStar_Syntax_Syntax.result_typ
                                                      = ret_t;
                                                    FStar_Syntax_Syntax.effect_args
                                                      = uu____3929;
                                                    FStar_Syntax_Syntax.flags
                                                      = []
                                                  } in
                                                FStar_Syntax_Syntax.mk_Comp
                                                  uu____3926 in
                                              let k =
                                                FStar_Syntax_Util.arrow
                                                  (FStar_List.append bs [f])
                                                  c in
                                              ((let uu____3995 =
                                                  FStar_All.pipe_left
                                                    (FStar_TypeChecker_Env.debug
                                                       env)
                                                    (FStar_Options.Other
                                                       "LayeredEffectsTc") in
                                                if uu____3995
                                                then
                                                  let uu____4000 =
                                                    FStar_Syntax_Print.term_to_string
                                                      k in
                                                  FStar_Util.print1
                                                    "Expected type of subcomp before unification: %s\n"
                                                    uu____4000
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
                                                   let uu____4008 =
                                                     FStar_All.pipe_right k
                                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                          env) in
                                                   FStar_All.pipe_right
                                                     uu____4008
                                                     (FStar_TypeChecker_Normalize.normalize
                                                        [FStar_TypeChecker_Env.Beta;
                                                        FStar_TypeChecker_Env.Eager_unfolding]
                                                        env) in
                                                 (let uu____4010 =
                                                    let uu____4011 =
                                                      FStar_Syntax_Subst.compress
                                                        k1 in
                                                    uu____4011.FStar_Syntax_Syntax.n in
                                                  match uu____4010 with
                                                  | FStar_Syntax_Syntax.Tm_arrow
                                                      (bs1, c1) ->
                                                      let uu____4036 =
                                                        FStar_Syntax_Subst.open_comp
                                                          bs1 c1 in
                                                      (match uu____4036 with
                                                       | (bs2, c2) ->
                                                           let res_t =
                                                             FStar_Syntax_Util.comp_result
                                                               c2 in
                                                           let uu____4046 =
                                                             let uu____4065 =
                                                               FStar_List.splitAt
                                                                 ((FStar_List.length
                                                                    bs2) -
                                                                    Prims.int_one)
                                                                 bs2 in
                                                             FStar_All.pipe_right
                                                               uu____4065
                                                               (fun
                                                                  uu____4142
                                                                  ->
                                                                  match uu____4142
                                                                  with
                                                                  | (l1, l2)
                                                                    ->
                                                                    let uu____4215
                                                                    =
                                                                    FStar_List.tl
                                                                    l1 in
                                                                    let uu____4230
                                                                    =
                                                                    FStar_List.hd
                                                                    l2 in
                                                                    (uu____4215,
                                                                    uu____4230)) in
                                                           (match uu____4046
                                                            with
                                                            | (bs3, f_b) ->
                                                                validate_layered_effect_binders
                                                                  env bs3
                                                                  [(FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                  res_t] r)));
                                                 (let uu____4289 =
                                                    FStar_All.pipe_right k1
                                                      (FStar_Syntax_Subst.close_univ_vars
                                                         stronger_us) in
                                                  (stronger_us, stronger_t,
                                                    uu____4289)))))))))))) in
             log_combinator "stronger_repr" stronger_repr;
             (let if_then_else =
                let if_then_else_ts =
                  let ts =
                    let uu____4329 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_layered_if_then_else_combinator in
                    FStar_All.pipe_right uu____4329 FStar_Util.must in
                  let uu____4366 =
                    let uu____4367 =
                      let uu____4370 =
                        FStar_All.pipe_right ts FStar_Pervasives_Native.snd in
                      FStar_All.pipe_right uu____4370
                        FStar_Syntax_Subst.compress in
                    uu____4367.FStar_Syntax_Syntax.n in
                  match uu____4366 with
                  | FStar_Syntax_Syntax.Tm_unknown ->
                      let signature_ts =
                        let uu____4388 = signature in
                        match uu____4388 with
                        | (us, t, uu____4403) -> (us, t) in
                      let uu____4420 =
                        FStar_TypeChecker_Env.inst_tscheme_with signature_ts
                          [FStar_Syntax_Syntax.U_unknown] in
                      (match uu____4420 with
                       | (uu____4431, signature_t) ->
                           let uu____4433 =
                             let uu____4434 =
                               FStar_Syntax_Subst.compress signature_t in
                             uu____4434.FStar_Syntax_Syntax.n in
                           (match uu____4433 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4444)
                                ->
                                let bs1 = FStar_Syntax_Subst.open_binders bs in
                                let repr_t =
                                  let repr_ts =
                                    let uu____4470 = repr in
                                    match uu____4470 with
                                    | (us, t, uu____4485) -> (us, t) in
                                  let uu____4502 =
                                    FStar_TypeChecker_Env.inst_tscheme_with
                                      repr_ts [FStar_Syntax_Syntax.U_unknown] in
                                  FStar_All.pipe_right uu____4502
                                    FStar_Pervasives_Native.snd in
                                let repr_t_applied =
                                  let uu____4522 =
                                    let uu____4523 =
                                      let uu____4540 =
                                        let uu____4551 =
                                          let uu____4554 =
                                            FStar_All.pipe_right bs1
                                              (FStar_List.map
                                                 FStar_Pervasives_Native.fst) in
                                          FStar_All.pipe_right uu____4554
                                            (FStar_List.map
                                               FStar_Syntax_Syntax.bv_to_name) in
                                        FStar_All.pipe_right uu____4551
                                          (FStar_List.map
                                             FStar_Syntax_Syntax.as_arg) in
                                      (repr_t, uu____4540) in
                                    FStar_Syntax_Syntax.Tm_app uu____4523 in
                                  FStar_Syntax_Syntax.mk uu____4522
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
                                let uu____4606 =
                                  FStar_Syntax_Util.abs
                                    (FStar_List.append bs1 [f_b; g_b; b_b])
                                    repr_t_applied
                                    FStar_Pervasives_Native.None in
                                ([], uu____4606)
                            | uu____4641 -> failwith "Impossible!"))
                  | uu____4649 -> ts in
                let r =
                  (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos in
                let uu____4653 =
                  check_and_gen1 "if_then_else" Prims.int_one if_then_else_ts in
                match uu____4653 with
                | (if_then_else_us, if_then_else_t, if_then_else_ty) ->
                    let uu____4677 =
                      FStar_Syntax_Subst.open_univ_vars if_then_else_us
                        if_then_else_t in
                    (match uu____4677 with
                     | (us, t) ->
                         let uu____4696 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_ty in
                         (match uu____4696 with
                          | (uu____4713, ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us in
                              (check_no_subtyping_for_layered_combinator env
                                 t (FStar_Pervasives_Native.Some ty);
                               (let uu____4717 = fresh_a_and_u_a "a" in
                                match uu____4717 with
                                | (a, u_a) ->
                                    let rest_bs =
                                      let uu____4746 =
                                        let uu____4747 =
                                          FStar_Syntax_Subst.compress ty in
                                        uu____4747.FStar_Syntax_Syntax.n in
                                      match uu____4746 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs, uu____4759) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (4))
                                          ->
                                          let uu____4787 =
                                            FStar_Syntax_Subst.open_binders
                                              bs in
                                          (match uu____4787 with
                                           | (a', uu____4797)::bs1 ->
                                               let uu____4817 =
                                                 let uu____4818 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           -
                                                           (Prims.of_int (3)))) in
                                                 FStar_All.pipe_right
                                                   uu____4818
                                                   FStar_Pervasives_Native.fst in
                                               let uu____4916 =
                                                 let uu____4929 =
                                                   let uu____4932 =
                                                     let uu____4933 =
                                                       let uu____4940 =
                                                         let uu____4943 =
                                                           FStar_All.pipe_right
                                                             a
                                                             FStar_Pervasives_Native.fst in
                                                         FStar_All.pipe_right
                                                           uu____4943
                                                           FStar_Syntax_Syntax.bv_to_name in
                                                       (a', uu____4940) in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____4933 in
                                                   [uu____4932] in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____4929 in
                                               FStar_All.pipe_right
                                                 uu____4817 uu____4916)
                                      | uu____4964 ->
                                          not_an_arrow_error "if_then_else"
                                            (Prims.of_int (4)) ty r in
                                    let bs = a :: rest_bs in
                                    let uu____4982 =
                                      let uu____4993 =
                                        let uu____4998 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs in
                                        let uu____4999 =
                                          let uu____5000 =
                                            FStar_All.pipe_right a
                                              FStar_Pervasives_Native.fst in
                                          FStar_All.pipe_right uu____5000
                                            FStar_Syntax_Syntax.bv_to_name in
                                        fresh_repr r uu____4998 u_a
                                          uu____4999 in
                                      match uu____4993 with
                                      | (repr1, g) ->
                                          let uu____5021 =
                                            let uu____5028 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1 in
                                            FStar_All.pipe_right uu____5028
                                              FStar_Syntax_Syntax.mk_binder in
                                          (uu____5021, g) in
                                    (match uu____4982 with
                                     | (f_bs, guard_f) ->
                                         let uu____5068 =
                                           let uu____5079 =
                                             let uu____5084 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs in
                                             let uu____5085 =
                                               let uu____5086 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst in
                                               FStar_All.pipe_right
                                                 uu____5086
                                                 FStar_Syntax_Syntax.bv_to_name in
                                             fresh_repr r uu____5084 u_a
                                               uu____5085 in
                                           match uu____5079 with
                                           | (repr1, g) ->
                                               let uu____5107 =
                                                 let uu____5114 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "g"
                                                     FStar_Pervasives_Native.None
                                                     repr1 in
                                                 FStar_All.pipe_right
                                                   uu____5114
                                                   FStar_Syntax_Syntax.mk_binder in
                                               (uu____5107, g) in
                                         (match uu____5068 with
                                          | (g_bs, guard_g) ->
                                              let p_b =
                                                let uu____5161 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "p"
                                                    FStar_Pervasives_Native.None
                                                    FStar_Syntax_Util.t_bool in
                                                FStar_All.pipe_right
                                                  uu____5161
                                                  FStar_Syntax_Syntax.mk_binder in
                                              let uu____5169 =
                                                let uu____5174 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [p_b]) in
                                                let uu____5193 =
                                                  let uu____5194 =
                                                    FStar_All.pipe_right a
                                                      FStar_Pervasives_Native.fst in
                                                  FStar_All.pipe_right
                                                    uu____5194
                                                    FStar_Syntax_Syntax.bv_to_name in
                                                fresh_repr r uu____5174 u_a
                                                  uu____5193 in
                                              (match uu____5169 with
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
                                                    (let k1 =
                                                       FStar_All.pipe_right k
                                                         (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                            env) in
                                                     (let uu____5256 =
                                                        let uu____5257 =
                                                          FStar_Syntax_Subst.compress
                                                            k1 in
                                                        uu____5257.FStar_Syntax_Syntax.n in
                                                      match uu____5256 with
                                                      | FStar_Syntax_Syntax.Tm_abs
                                                          (bs1, body,
                                                           uu____5262)
                                                          ->
                                                          let uu____5287 =
                                                            FStar_Syntax_Subst.open_term
                                                              bs1 body in
                                                          (match uu____5287
                                                           with
                                                           | (bs2, body1) ->
                                                               let uu____5294
                                                                 =
                                                                 let uu____5321
                                                                   =
                                                                   FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (3)))
                                                                    bs2 in
                                                                 FStar_All.pipe_right
                                                                   uu____5321
                                                                   (fun
                                                                    uu____5407
                                                                    ->
                                                                    match uu____5407
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____5488
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l1
                                                                    FStar_List.tl in
                                                                    let uu____5519
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____5546
                                                                    =
                                                                    let uu____5553
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____5553
                                                                    FStar_List.hd in
                                                                    (uu____5488,
                                                                    uu____5519,
                                                                    uu____5546)) in
                                                               (match uu____5294
                                                                with
                                                                | (bs3, f_b,
                                                                   g_b) ->
                                                                    validate_layered_effect_binders
                                                                    env bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort;
                                                                    body1] r)));
                                                     (let uu____5671 =
                                                        FStar_All.pipe_right
                                                          k1
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             if_then_else_us) in
                                                      (if_then_else_us,
                                                        uu____5671,
                                                        if_then_else_ty))))))))))) in
              log_combinator "if_then_else" if_then_else;
              (let r =
                 let uu____5686 =
                   let uu____5689 =
                     let uu____5698 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_layered_if_then_else_combinator in
                     FStar_All.pipe_right uu____5698 FStar_Util.must in
                   FStar_All.pipe_right uu____5689
                     FStar_Pervasives_Native.snd in
                 uu____5686.FStar_Syntax_Syntax.pos in
               let binder_aq_to_arg_aq aq =
                 match aq with
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                     uu____5773) -> aq
                 | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
                     uu____5775) ->
                     FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.Implicit false)
                 | uu____5777 -> FStar_Pervasives_Native.None in
               let uu____5780 = if_then_else in
               match uu____5780 with
               | (ite_us, ite_t, uu____5795) ->
                   let uu____5808 =
                     FStar_Syntax_Subst.open_univ_vars ite_us ite_t in
                   (match uu____5808 with
                    | (us, ite_t1) ->
                        let uu____5815 =
                          let uu____5832 =
                            let uu____5833 =
                              FStar_Syntax_Subst.compress ite_t1 in
                            uu____5833.FStar_Syntax_Syntax.n in
                          match uu____5832 with
                          | FStar_Syntax_Syntax.Tm_abs
                              (bs, uu____5853, uu____5854) ->
                              let bs1 = FStar_Syntax_Subst.open_binders bs in
                              let uu____5880 =
                                let uu____5893 =
                                  let uu____5898 =
                                    let uu____5901 =
                                      let uu____5910 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                (Prims.of_int (3)))) in
                                      FStar_All.pipe_right uu____5910
                                        FStar_Pervasives_Native.snd in
                                    FStar_All.pipe_right uu____5901
                                      (FStar_List.map
                                         FStar_Pervasives_Native.fst) in
                                  FStar_All.pipe_right uu____5898
                                    (FStar_List.map
                                       FStar_Syntax_Syntax.bv_to_name) in
                                FStar_All.pipe_right uu____5893
                                  (fun l ->
                                     let uu____6066 = l in
                                     match uu____6066 with
                                     | f::g::p::[] -> (f, g, p)) in
                              (match uu____5880 with
                               | (f, g, p) ->
                                   let uu____6137 =
                                     let uu____6138 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env0 us in
                                     FStar_TypeChecker_Env.push_binders
                                       uu____6138 bs1 in
                                   let uu____6139 =
                                     let uu____6140 =
                                       FStar_All.pipe_right bs1
                                         (FStar_List.map
                                            (fun uu____6165 ->
                                               match uu____6165 with
                                               | (b, qual) ->
                                                   let uu____6184 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       b in
                                                   (uu____6184,
                                                     (binder_aq_to_arg_aq
                                                        qual)))) in
                                     FStar_Syntax_Syntax.mk_Tm_app ite_t1
                                       uu____6140 r in
                                   (uu____6137, uu____6139, f, g, p))
                          | uu____6193 ->
                              failwith
                                "Impossible! ite_t must have been an abstraction with at least 3 binders" in
                        (match uu____5815 with
                         | (env, ite_t_applied, f_t, g_t, p_t) ->
                             let uu____6228 =
                               let uu____6237 = stronger_repr in
                               match uu____6237 with
                               | (uu____6258, subcomp_t, subcomp_ty) ->
                                   let uu____6273 =
                                     FStar_Syntax_Subst.open_univ_vars us
                                       subcomp_t in
                                   (match uu____6273 with
                                    | (uu____6286, subcomp_t1) ->
                                        let uu____6288 =
                                          let uu____6299 =
                                            FStar_Syntax_Subst.open_univ_vars
                                              us subcomp_ty in
                                          match uu____6299 with
                                          | (uu____6314, subcomp_ty1) ->
                                              let uu____6316 =
                                                let uu____6317 =
                                                  FStar_Syntax_Subst.compress
                                                    subcomp_ty1 in
                                                uu____6317.FStar_Syntax_Syntax.n in
                                              (match uu____6316 with
                                               | FStar_Syntax_Syntax.Tm_arrow
                                                   (bs, uu____6331) ->
                                                   let uu____6352 =
                                                     FStar_All.pipe_right bs
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs)
                                                             - Prims.int_one)) in
                                                   (match uu____6352 with
                                                    | (bs_except_last,
                                                       last_b) ->
                                                        let uu____6458 =
                                                          FStar_All.pipe_right
                                                            bs_except_last
                                                            (FStar_List.map
                                                               FStar_Pervasives_Native.snd) in
                                                        let uu____6485 =
                                                          let uu____6488 =
                                                            FStar_All.pipe_right
                                                              last_b
                                                              FStar_List.hd in
                                                          FStar_All.pipe_right
                                                            uu____6488
                                                            FStar_Pervasives_Native.snd in
                                                        (uu____6458,
                                                          uu____6485))
                                               | uu____6531 ->
                                                   failwith
                                                     "Impossible! subcomp_ty must have been an arrow with at lease 1 binder") in
                                        (match uu____6288 with
                                         | (aqs_except_last, last_aq) ->
                                             let uu____6565 =
                                               let uu____6576 =
                                                 FStar_All.pipe_right
                                                   aqs_except_last
                                                   (FStar_List.map
                                                      binder_aq_to_arg_aq) in
                                               let uu____6593 =
                                                 FStar_All.pipe_right last_aq
                                                   binder_aq_to_arg_aq in
                                               (uu____6576, uu____6593) in
                                             (match uu____6565 with
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
                                                  let uu____6705 = aux f_t in
                                                  let uu____6708 = aux g_t in
                                                  (uu____6705, uu____6708)))) in
                             (match uu____6228 with
                              | (subcomp_f, subcomp_g) ->
                                  let uu____6725 =
                                    let aux t =
                                      let uu____6742 =
                                        let uu____6743 =
                                          let uu____6770 =
                                            let uu____6787 =
                                              let uu____6796 =
                                                FStar_Syntax_Syntax.mk_Total
                                                  ite_t_applied in
                                              FStar_Util.Inr uu____6796 in
                                            (uu____6787,
                                              FStar_Pervasives_Native.None) in
                                          (t, uu____6770,
                                            FStar_Pervasives_Native.None) in
                                        FStar_Syntax_Syntax.Tm_ascribed
                                          uu____6743 in
                                      FStar_Syntax_Syntax.mk uu____6742 r in
                                    let uu____6837 = aux subcomp_f in
                                    let uu____6838 = aux subcomp_g in
                                    (uu____6837, uu____6838) in
                                  (match uu____6725 with
                                   | (tm_subcomp_ascribed_f,
                                      tm_subcomp_ascribed_g) ->
                                       ((let uu____6842 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug env)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____6842
                                         then
                                           let uu____6847 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_f in
                                           let uu____6849 =
                                             FStar_Syntax_Print.term_to_string
                                               tm_subcomp_ascribed_g in
                                           FStar_Util.print2
                                             "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                             uu____6847 uu____6849
                                         else ());
                                        (let uu____6854 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env tm_subcomp_ascribed_f in
                                         match uu____6854 with
                                         | (uu____6861, uu____6862, g_f) ->
                                             let g_f1 =
                                               let uu____6865 =
                                                 let uu____6866 =
                                                   let uu____6867 =
                                                     FStar_All.pipe_right p_t
                                                       FStar_Syntax_Util.b2t in
                                                   FStar_All.pipe_right
                                                     uu____6867
                                                     (fun uu____6870 ->
                                                        FStar_TypeChecker_Common.NonTrivial
                                                          uu____6870) in
                                                 FStar_TypeChecker_Env.guard_of_guard_formula
                                                   uu____6866 in
                                               FStar_TypeChecker_Env.imp_guard
                                                 uu____6865 g_f in
                                             (FStar_TypeChecker_Rel.force_trivial_guard
                                                env g_f1;
                                              (let uu____6872 =
                                                 FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                   env tm_subcomp_ascribed_g in
                                               match uu____6872 with
                                               | (uu____6879, uu____6880,
                                                  g_g) ->
                                                   let g_g1 =
                                                     let not_p =
                                                       let uu____6884 =
                                                         let uu____6885 =
                                                           FStar_Syntax_Syntax.lid_as_fv
                                                             FStar_Parser_Const.not_lid
                                                             FStar_Syntax_Syntax.delta_constant
                                                             FStar_Pervasives_Native.None in
                                                         FStar_All.pipe_right
                                                           uu____6885
                                                           FStar_Syntax_Syntax.fv_to_tm in
                                                       let uu____6886 =
                                                         let uu____6887 =
                                                           let uu____6896 =
                                                             FStar_All.pipe_right
                                                               p_t
                                                               FStar_Syntax_Util.b2t in
                                                           FStar_All.pipe_right
                                                             uu____6896
                                                             FStar_Syntax_Syntax.as_arg in
                                                         [uu____6887] in
                                                       FStar_Syntax_Syntax.mk_Tm_app
                                                         uu____6884
                                                         uu____6886 r in
                                                     let uu____6923 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         (FStar_TypeChecker_Common.NonTrivial
                                                            not_p) in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____6923 g_g in
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
                   (let uu____6947 =
                      let uu____6953 =
                        let uu____6955 =
                          FStar_Ident.string_of_lid
                            ed.FStar_Syntax_Syntax.mname in
                        let uu____6957 =
                          FStar_Ident.string_of_lid
                            act.FStar_Syntax_Syntax.action_name in
                        let uu____6959 =
                          FStar_Syntax_Print.binders_to_string "; "
                            act.FStar_Syntax_Syntax.action_params in
                        FStar_Util.format3
                          "Action %s:%s has non-empty action params (%s)"
                          uu____6955 uu____6957 uu____6959 in
                      (FStar_Errors.Fatal_MalformedActionDeclaration,
                        uu____6953) in
                    FStar_Errors.raise_error uu____6947 r)
                 else ();
                 (let uu____6966 =
                    let uu____6971 =
                      FStar_Syntax_Subst.univ_var_opening
                        act.FStar_Syntax_Syntax.action_univs in
                    match uu____6971 with
                    | (usubst, us) ->
                        let uu____6994 =
                          FStar_TypeChecker_Env.push_univ_vars env us in
                        let uu____6995 =
                          let uu___620_6996 = act in
                          let uu____6997 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_defn in
                          let uu____6998 =
                            FStar_Syntax_Subst.subst usubst
                              act.FStar_Syntax_Syntax.action_typ in
                          {
                            FStar_Syntax_Syntax.action_name =
                              (uu___620_6996.FStar_Syntax_Syntax.action_name);
                            FStar_Syntax_Syntax.action_unqualified_name =
                              (uu___620_6996.FStar_Syntax_Syntax.action_unqualified_name);
                            FStar_Syntax_Syntax.action_univs = us;
                            FStar_Syntax_Syntax.action_params =
                              (uu___620_6996.FStar_Syntax_Syntax.action_params);
                            FStar_Syntax_Syntax.action_defn = uu____6997;
                            FStar_Syntax_Syntax.action_typ = uu____6998
                          } in
                        (uu____6994, uu____6995) in
                  match uu____6966 with
                  | (env1, act1) ->
                      let act_typ =
                        let uu____7002 =
                          let uu____7003 =
                            FStar_Syntax_Subst.compress
                              act1.FStar_Syntax_Syntax.action_typ in
                          uu____7003.FStar_Syntax_Syntax.n in
                        match uu____7002 with
                        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                            let ct = FStar_Syntax_Util.comp_to_comp_typ c in
                            let uu____7029 =
                              FStar_Ident.lid_equals
                                ct.FStar_Syntax_Syntax.effect_name
                                ed.FStar_Syntax_Syntax.mname in
                            if uu____7029
                            then
                              let repr_ts =
                                let uu____7033 = repr in
                                match uu____7033 with
                                | (us, t, uu____7048) -> (us, t) in
                              let repr1 =
                                let uu____7066 =
                                  FStar_TypeChecker_Env.inst_tscheme_with
                                    repr_ts ct.FStar_Syntax_Syntax.comp_univs in
                                FStar_All.pipe_right uu____7066
                                  FStar_Pervasives_Native.snd in
                              let repr2 =
                                let uu____7076 =
                                  let uu____7077 =
                                    FStar_Syntax_Syntax.as_arg
                                      ct.FStar_Syntax_Syntax.result_typ in
                                  uu____7077 ::
                                    (ct.FStar_Syntax_Syntax.effect_args) in
                                FStar_Syntax_Syntax.mk_Tm_app repr1
                                  uu____7076 r in
                              let c1 =
                                let uu____7095 =
                                  let uu____7098 =
                                    FStar_TypeChecker_Env.new_u_univ () in
                                  FStar_Pervasives_Native.Some uu____7098 in
                                FStar_Syntax_Syntax.mk_Total' repr2
                                  uu____7095 in
                              FStar_Syntax_Util.arrow bs c1
                            else act1.FStar_Syntax_Syntax.action_typ
                        | uu____7101 -> act1.FStar_Syntax_Syntax.action_typ in
                      let uu____7102 =
                        FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term env1
                          act_typ in
                      (match uu____7102 with
                       | (act_typ1, uu____7110, g_t) ->
                           let uu____7112 =
                             let uu____7119 =
                               let uu___645_7120 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   act_typ1 in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___645_7120.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___645_7120.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___645_7120.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___645_7120.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___645_7120.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___645_7120.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___645_7120.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___645_7120.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___645_7120.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___645_7120.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   false;
                                 FStar_TypeChecker_Env.effects =
                                   (uu___645_7120.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___645_7120.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs =
                                   (uu___645_7120.FStar_TypeChecker_Env.letrecs);
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___645_7120.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___645_7120.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___645_7120.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.use_eq_strict =
                                   (uu___645_7120.FStar_TypeChecker_Env.use_eq_strict);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___645_7120.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___645_7120.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___645_7120.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___645_7120.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___645_7120.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___645_7120.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___645_7120.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___645_7120.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___645_7120.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___645_7120.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___645_7120.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___645_7120.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___645_7120.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___645_7120.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___645_7120.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___645_7120.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___645_7120.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___645_7120.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___645_7120.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___645_7120.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.mpreprocess =
                                   (uu___645_7120.FStar_TypeChecker_Env.mpreprocess);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___645_7120.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___645_7120.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___645_7120.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___645_7120.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___645_7120.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___645_7120.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___645_7120.FStar_TypeChecker_Env.erasable_types_tab);
                                 FStar_TypeChecker_Env.enable_defer_to_tac =
                                   (uu___645_7120.FStar_TypeChecker_Env.enable_defer_to_tac)
                               } in
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               uu____7119
                               act1.FStar_Syntax_Syntax.action_defn in
                           (match uu____7112 with
                            | (act_defn, uu____7123, g_d) ->
                                ((let uu____7126 =
                                    FStar_All.pipe_left
                                      (FStar_TypeChecker_Env.debug env1)
                                      (FStar_Options.Other "LayeredEffectsTc") in
                                  if uu____7126
                                  then
                                    let uu____7131 =
                                      FStar_Syntax_Print.term_to_string
                                        act_defn in
                                    let uu____7133 =
                                      FStar_Syntax_Print.term_to_string
                                        act_typ1 in
                                    FStar_Util.print2
                                      "Typechecked action definition: %s and action type: %s\n"
                                      uu____7131 uu____7133
                                  else ());
                                 (let uu____7138 =
                                    let act_typ2 =
                                      FStar_TypeChecker_Normalize.normalize
                                        [FStar_TypeChecker_Env.Beta] env1
                                        act_typ1 in
                                    let uu____7146 =
                                      let uu____7147 =
                                        FStar_Syntax_Subst.compress act_typ2 in
                                      uu____7147.FStar_Syntax_Syntax.n in
                                    match uu____7146 with
                                    | FStar_Syntax_Syntax.Tm_arrow
                                        (bs, uu____7157) ->
                                        let bs1 =
                                          FStar_Syntax_Subst.open_binders bs in
                                        let env2 =
                                          FStar_TypeChecker_Env.push_binders
                                            env1 bs1 in
                                        let uu____7180 =
                                          FStar_Syntax_Util.type_u () in
                                        (match uu____7180 with
                                         | (t, u) ->
                                             let reason =
                                               let uu____7195 =
                                                 FStar_Ident.string_of_lid
                                                   ed.FStar_Syntax_Syntax.mname in
                                               let uu____7197 =
                                                 FStar_Ident.string_of_lid
                                                   act1.FStar_Syntax_Syntax.action_name in
                                               FStar_Util.format2
                                                 "implicit for return type of action %s:%s"
                                                 uu____7195 uu____7197 in
                                             let uu____7200 =
                                               FStar_TypeChecker_Util.new_implicit_var
                                                 reason r env2 t in
                                             (match uu____7200 with
                                              | (a_tm, uu____7220, g_tm) ->
                                                  let uu____7234 =
                                                    fresh_repr r env2 u a_tm in
                                                  (match uu____7234 with
                                                   | (repr1, g) ->
                                                       let uu____7247 =
                                                         let uu____7250 =
                                                           let uu____7253 =
                                                             let uu____7256 =
                                                               FStar_TypeChecker_Env.new_u_univ
                                                                 () in
                                                             FStar_All.pipe_right
                                                               uu____7256
                                                               (fun
                                                                  uu____7259
                                                                  ->
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____7259) in
                                                           FStar_Syntax_Syntax.mk_Total'
                                                             repr1 uu____7253 in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____7250 in
                                                       let uu____7260 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g g_tm in
                                                       (uu____7247,
                                                         uu____7260))))
                                    | uu____7263 ->
                                        let uu____7264 =
                                          let uu____7270 =
                                            let uu____7272 =
                                              FStar_Ident.string_of_lid
                                                ed.FStar_Syntax_Syntax.mname in
                                            let uu____7274 =
                                              FStar_Ident.string_of_lid
                                                act1.FStar_Syntax_Syntax.action_name in
                                            let uu____7276 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.format3
                                              "Unexpected non-function type for action %s:%s (%s)"
                                              uu____7272 uu____7274
                                              uu____7276 in
                                          (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                            uu____7270) in
                                        FStar_Errors.raise_error uu____7264 r in
                                  match uu____7138 with
                                  | (k, g_k) ->
                                      ((let uu____7293 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug env1)
                                            (FStar_Options.Other
                                               "LayeredEffectsTc") in
                                        if uu____7293
                                        then
                                          let uu____7298 =
                                            FStar_Syntax_Print.term_to_string
                                              k in
                                          FStar_Util.print1
                                            "Expected action type: %s\n"
                                            uu____7298
                                        else ());
                                       (let g =
                                          FStar_TypeChecker_Rel.teq env1
                                            act_typ1 k in
                                        FStar_List.iter
                                          (FStar_TypeChecker_Rel.force_trivial_guard
                                             env1) [g_t; g_d; g_k; g];
                                        (let uu____7306 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env1)
                                             (FStar_Options.Other
                                                "LayeredEffectsTc") in
                                         if uu____7306
                                         then
                                           let uu____7311 =
                                             FStar_Syntax_Print.term_to_string
                                               k in
                                           FStar_Util.print1
                                             "Expected action type after unification: %s\n"
                                             uu____7311
                                         else ());
                                        (let act_typ2 =
                                           let err_msg t =
                                             let uu____7324 =
                                               FStar_Ident.string_of_lid
                                                 ed.FStar_Syntax_Syntax.mname in
                                             let uu____7326 =
                                               FStar_Ident.string_of_lid
                                                 act1.FStar_Syntax_Syntax.action_name in
                                             let uu____7328 =
                                               FStar_Syntax_Print.term_to_string
                                                 t in
                                             FStar_Util.format3
                                               "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                               uu____7324 uu____7326
                                               uu____7328 in
                                           let repr_args t =
                                             let uu____7349 =
                                               let uu____7350 =
                                                 FStar_Syntax_Subst.compress
                                                   t in
                                               uu____7350.FStar_Syntax_Syntax.n in
                                             match uu____7349 with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (head, a::is) ->
                                                 let uu____7402 =
                                                   let uu____7403 =
                                                     FStar_Syntax_Subst.compress
                                                       head in
                                                   uu____7403.FStar_Syntax_Syntax.n in
                                                 (match uu____7402 with
                                                  | FStar_Syntax_Syntax.Tm_uinst
                                                      (uu____7412, us) ->
                                                      (us,
                                                        (FStar_Pervasives_Native.fst
                                                           a), is)
                                                  | uu____7422 ->
                                                      let uu____7423 =
                                                        let uu____7429 =
                                                          err_msg t in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____7429) in
                                                      FStar_Errors.raise_error
                                                        uu____7423 r)
                                             | uu____7438 ->
                                                 let uu____7439 =
                                                   let uu____7445 = err_msg t in
                                                   (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                     uu____7445) in
                                                 FStar_Errors.raise_error
                                                   uu____7439 r in
                                           let k1 =
                                             FStar_TypeChecker_Normalize.normalize
                                               [FStar_TypeChecker_Env.Beta]
                                               env1 k in
                                           let uu____7455 =
                                             let uu____7456 =
                                               FStar_Syntax_Subst.compress k1 in
                                             uu____7456.FStar_Syntax_Syntax.n in
                                           match uu____7455 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs, c) ->
                                               let uu____7481 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs c in
                                               (match uu____7481 with
                                                | (bs1, c1) ->
                                                    let uu____7488 =
                                                      repr_args
                                                        (FStar_Syntax_Util.comp_result
                                                           c1) in
                                                    (match uu____7488 with
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
                                                         let uu____7499 =
                                                           FStar_Syntax_Syntax.mk_Comp
                                                             ct in
                                                         FStar_Syntax_Util.arrow
                                                           bs1 uu____7499))
                                           | uu____7502 ->
                                               let uu____7503 =
                                                 let uu____7509 = err_msg k1 in
                                                 (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                   uu____7509) in
                                               FStar_Errors.raise_error
                                                 uu____7503 r in
                                         (let uu____7513 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env1)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____7513
                                          then
                                            let uu____7518 =
                                              FStar_Syntax_Print.term_to_string
                                                act_typ2 in
                                            FStar_Util.print1
                                              "Action type after injecting it into the monad: %s\n"
                                              uu____7518
                                          else ());
                                         (let act2 =
                                            let uu____7524 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env1 act_defn in
                                            match uu____7524 with
                                            | (us, act_defn1) ->
                                                if
                                                  act1.FStar_Syntax_Syntax.action_univs
                                                    = []
                                                then
                                                  let uu___718_7538 = act1 in
                                                  let uu____7539 =
                                                    FStar_Syntax_Subst.close_univ_vars
                                                      us act_typ2 in
                                                  {
                                                    FStar_Syntax_Syntax.action_name
                                                      =
                                                      (uu___718_7538.FStar_Syntax_Syntax.action_name);
                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                      =
                                                      (uu___718_7538.FStar_Syntax_Syntax.action_unqualified_name);
                                                    FStar_Syntax_Syntax.action_univs
                                                      = us;
                                                    FStar_Syntax_Syntax.action_params
                                                      =
                                                      (uu___718_7538.FStar_Syntax_Syntax.action_params);
                                                    FStar_Syntax_Syntax.action_defn
                                                      = act_defn1;
                                                    FStar_Syntax_Syntax.action_typ
                                                      = uu____7539
                                                  }
                                                else
                                                  (let uu____7542 =
                                                     ((FStar_List.length us)
                                                        =
                                                        (FStar_List.length
                                                           act1.FStar_Syntax_Syntax.action_univs))
                                                       &&
                                                       (FStar_List.forall2
                                                          (fun u1 ->
                                                             fun u2 ->
                                                               let uu____7549
                                                                 =
                                                                 FStar_Syntax_Syntax.order_univ_name
                                                                   u1 u2 in
                                                               uu____7549 =
                                                                 Prims.int_zero)
                                                          us
                                                          act1.FStar_Syntax_Syntax.action_univs) in
                                                   if uu____7542
                                                   then
                                                     let uu___723_7554 = act1 in
                                                     let uu____7555 =
                                                       FStar_Syntax_Subst.close_univ_vars
                                                         act1.FStar_Syntax_Syntax.action_univs
                                                         act_typ2 in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         =
                                                         (uu___723_7554.FStar_Syntax_Syntax.action_name);
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         =
                                                         (uu___723_7554.FStar_Syntax_Syntax.action_unqualified_name);
                                                       FStar_Syntax_Syntax.action_univs
                                                         =
                                                         (uu___723_7554.FStar_Syntax_Syntax.action_univs);
                                                       FStar_Syntax_Syntax.action_params
                                                         =
                                                         (uu___723_7554.FStar_Syntax_Syntax.action_params);
                                                       FStar_Syntax_Syntax.action_defn
                                                         = act_defn1;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____7555
                                                     }
                                                   else
                                                     (let uu____7558 =
                                                        let uu____7564 =
                                                          let uu____7566 =
                                                            FStar_Ident.string_of_lid
                                                              ed.FStar_Syntax_Syntax.mname in
                                                          let uu____7568 =
                                                            FStar_Ident.string_of_lid
                                                              act1.FStar_Syntax_Syntax.action_name in
                                                          let uu____7570 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              us in
                                                          let uu____7572 =
                                                            FStar_Syntax_Print.univ_names_to_string
                                                              act1.FStar_Syntax_Syntax.action_univs in
                                                          FStar_Util.format4
                                                            "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                            uu____7566
                                                            uu____7568
                                                            uu____7570
                                                            uu____7572 in
                                                        (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                          uu____7564) in
                                                      FStar_Errors.raise_error
                                                        uu____7558 r)) in
                                          act2))))))))) in
               let tschemes_of uu____7597 =
                 match uu____7597 with | (us, t, ty) -> ((us, t), (us, ty)) in
               let combinators =
                 let uu____7642 =
                   let uu____7643 = tschemes_of repr in
                   let uu____7648 = tschemes_of return_repr in
                   let uu____7653 = tschemes_of bind_repr in
                   let uu____7658 = tschemes_of stronger_repr in
                   let uu____7663 = tschemes_of if_then_else in
                   {
                     FStar_Syntax_Syntax.l_repr = uu____7643;
                     FStar_Syntax_Syntax.l_return = uu____7648;
                     FStar_Syntax_Syntax.l_bind = uu____7653;
                     FStar_Syntax_Syntax.l_subcomp = uu____7658;
                     FStar_Syntax_Syntax.l_if_then_else = uu____7663
                   } in
                 FStar_Syntax_Syntax.Layered_eff uu____7642 in
               let uu___732_7668 = ed in
               let uu____7669 =
                 FStar_List.map (tc_action env0)
                   ed.FStar_Syntax_Syntax.actions in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___732_7668.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___732_7668.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs =
                   (uu___732_7668.FStar_Syntax_Syntax.univs);
                 FStar_Syntax_Syntax.binders =
                   (uu___732_7668.FStar_Syntax_Syntax.binders);
                 FStar_Syntax_Syntax.signature =
                   (let uu____7676 = signature in
                    match uu____7676 with | (us, t, uu____7691) -> (us, t));
                 FStar_Syntax_Syntax.combinators = combinators;
                 FStar_Syntax_Syntax.actions = uu____7669;
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___732_7668.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____7729 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED") in
         if uu____7729
         then
           let uu____7734 = FStar_Syntax_Print.eff_decl_to_string false ed in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____7734
         else ());
        (let uu____7740 =
           let uu____7745 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs in
           match uu____7745 with
           | (ed_univs_subst, ed_univs) ->
               let bs =
                 let uu____7769 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders in
                 FStar_Syntax_Subst.open_binders uu____7769 in
               let uu____7770 =
                 let uu____7777 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____7777 bs in
               (match uu____7770 with
                | (bs1, uu____7783, uu____7784) ->
                    let uu____7785 =
                      let tmp_t =
                        let uu____7795 =
                          let uu____7798 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun uu____7803 ->
                                 FStar_Pervasives_Native.Some uu____7803) in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____7798 in
                        FStar_Syntax_Util.arrow bs1 uu____7795 in
                      let uu____7804 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t in
                      match uu____7804 with
                      | (us, tmp_t1) ->
                          let uu____7821 =
                            let uu____7822 =
                              let uu____7823 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals in
                              FStar_All.pipe_right uu____7823
                                FStar_Pervasives_Native.fst in
                            FStar_All.pipe_right uu____7822
                              FStar_Syntax_Subst.close_binders in
                          (us, uu____7821) in
                    (match uu____7785 with
                     | (us, bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____7860 ->
                              let uu____7863 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1 ->
                                        fun u2 ->
                                          let uu____7870 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2 in
                                          uu____7870 = Prims.int_zero)
                                     ed_univs us) in
                              if uu____7863
                              then (us, bs2)
                              else
                                (let uu____7881 =
                                   let uu____7887 =
                                     let uu____7889 =
                                       FStar_Ident.string_of_lid
                                         ed.FStar_Syntax_Syntax.mname in
                                     let uu____7891 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs) in
                                     let uu____7893 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us) in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       uu____7889 uu____7891 uu____7893 in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____7887) in
                                 let uu____7897 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname in
                                 FStar_Errors.raise_error uu____7881
                                   uu____7897)))) in
         match uu____7740 with
         | (us, bs) ->
             let ed1 =
               let uu___766_7905 = ed in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___766_7905.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___766_7905.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___766_7905.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___766_7905.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___766_7905.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___766_7905.FStar_Syntax_Syntax.eff_attrs)
               } in
             let uu____7906 = FStar_Syntax_Subst.univ_var_opening us in
             (match uu____7906 with
              | (ed_univs_subst, ed_univs) ->
                  let uu____7925 =
                    let uu____7930 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs in
                    FStar_Syntax_Subst.open_binders' uu____7930 in
                  (match uu____7925 with
                   | (ed_bs, ed_bs_subst) ->
                       let ed2 =
                         let op uu____7951 =
                           match uu____7951 with
                           | (us1, t) ->
                               let t1 =
                                 let uu____7971 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst in
                                 FStar_Syntax_Subst.subst uu____7971 t in
                               let uu____7980 =
                                 let uu____7981 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst in
                                 FStar_Syntax_Subst.subst uu____7981 t1 in
                               (us1, uu____7980) in
                         let uu___780_7986 = ed1 in
                         let uu____7987 =
                           op ed1.FStar_Syntax_Syntax.signature in
                         let uu____7988 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators in
                         let uu____7989 =
                           FStar_List.map
                             (fun a ->
                                let uu___783_7997 = a in
                                let uu____7998 =
                                  let uu____7999 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn)) in
                                  FStar_Pervasives_Native.snd uu____7999 in
                                let uu____8010 =
                                  let uu____8011 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ)) in
                                  FStar_Pervasives_Native.snd uu____8011 in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___783_7997.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___783_7997.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___783_7997.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___783_7997.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____7998;
                                  FStar_Syntax_Syntax.action_typ = uu____8010
                                }) ed1.FStar_Syntax_Syntax.actions in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___780_7986.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___780_7986.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___780_7986.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___780_7986.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____7987;
                           FStar_Syntax_Syntax.combinators = uu____7988;
                           FStar_Syntax_Syntax.actions = uu____7989;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___780_7986.FStar_Syntax_Syntax.eff_attrs)
                         } in
                       ((let uu____8023 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED") in
                         if uu____8023
                         then
                           let uu____8028 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2 in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____8028
                         else ());
                        (let env =
                           let uu____8035 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs in
                           FStar_TypeChecker_Env.push_binders uu____8035
                             ed_bs in
                         let check_and_gen' comb n env_opt uu____8070 k =
                           match uu____8070 with
                           | (us1, t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env in
                               let uu____8090 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t in
                               (match uu____8090 with
                                | (us2, t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____8099 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2 in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____8099 t1 k1
                                      | FStar_Pervasives_Native.None ->
                                          let uu____8100 =
                                            let uu____8107 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2 in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____8107 t1 in
                                          (match uu____8100 with
                                           | (t2, uu____8109, g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2)) in
                                    let uu____8112 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2 in
                                    (match uu____8112 with
                                     | (g_us, t3) ->
                                         (if (FStar_List.length g_us) <> n
                                          then
                                            (let error =
                                               let uu____8128 =
                                                 FStar_Ident.string_of_lid
                                                   ed2.FStar_Syntax_Syntax.mname in
                                               let uu____8130 =
                                                 FStar_Util.string_of_int n in
                                               let uu____8132 =
                                                 let uu____8134 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length in
                                                 FStar_All.pipe_right
                                                   uu____8134
                                                   FStar_Util.string_of_int in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 uu____8128 comb uu____8130
                                                 uu____8132 in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____8149 ->
                                               let uu____8150 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1 ->
                                                         fun u2 ->
                                                           let uu____8157 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2 in
                                                           uu____8157 =
                                                             Prims.int_zero)
                                                      us2 g_us) in
                                               if uu____8150
                                               then (g_us, t3)
                                               else
                                                 (let uu____8168 =
                                                    let uu____8174 =
                                                      let uu____8176 =
                                                        FStar_Ident.string_of_lid
                                                          ed2.FStar_Syntax_Syntax.mname in
                                                      let uu____8178 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2) in
                                                      let uu____8180 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us) in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        uu____8176 comb
                                                        uu____8178 uu____8180 in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____8174) in
                                                  FStar_Errors.raise_error
                                                    uu____8168
                                                    t3.FStar_Syntax_Syntax.pos))))) in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None in
                         (let uu____8188 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED") in
                          if uu____8188
                          then
                            let uu____8193 =
                              FStar_Syntax_Print.tscheme_to_string signature in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____8193
                          else ());
                         (let fresh_a_and_wp uu____8209 =
                            let fail t =
                              let uu____8222 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t in
                              FStar_Errors.raise_error uu____8222
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos in
                            let uu____8238 =
                              FStar_TypeChecker_Env.inst_tscheme signature in
                            match uu____8238 with
                            | (uu____8249, signature1) ->
                                let uu____8251 =
                                  let uu____8252 =
                                    FStar_Syntax_Subst.compress signature1 in
                                  uu____8252.FStar_Syntax_Syntax.n in
                                (match uu____8251 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1, uu____8262) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1 in
                                     (match bs2 with
                                      | (a, uu____8291)::(wp, uu____8293)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____8322 -> fail signature1)
                                 | uu____8323 -> fail signature1) in
                          let log_combinator s ts =
                            let uu____8337 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED") in
                            if uu____8337
                            then
                              let uu____8342 =
                                FStar_Ident.string_of_lid
                                  ed2.FStar_Syntax_Syntax.mname in
                              let uu____8344 =
                                FStar_Syntax_Print.tscheme_to_string ts in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                uu____8342 s uu____8344
                            else () in
                          let ret_wp =
                            let uu____8350 = fresh_a_and_wp () in
                            match uu____8350 with
                            | (a, wp_sort) ->
                                let k =
                                  let uu____8366 =
                                    let uu____8375 =
                                      FStar_Syntax_Syntax.mk_binder a in
                                    let uu____8382 =
                                      let uu____8391 =
                                        let uu____8398 =
                                          FStar_Syntax_Syntax.bv_to_name a in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____8398 in
                                      [uu____8391] in
                                    uu____8375 :: uu____8382 in
                                  let uu____8417 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort in
                                  FStar_Syntax_Util.arrow uu____8366
                                    uu____8417 in
                                let uu____8420 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____8420
                                  (FStar_Pervasives_Native.Some k) in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____8434 = fresh_a_and_wp () in
                             match uu____8434 with
                             | (a, wp_sort_a) ->
                                 let uu____8447 = fresh_a_and_wp () in
                                 (match uu____8447 with
                                  | (b, wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____8463 =
                                          let uu____8472 =
                                            let uu____8479 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____8479 in
                                          [uu____8472] in
                                        let uu____8492 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____8463
                                          uu____8492 in
                                      let k =
                                        let uu____8498 =
                                          let uu____8507 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range in
                                          let uu____8514 =
                                            let uu____8523 =
                                              FStar_Syntax_Syntax.mk_binder a in
                                            let uu____8530 =
                                              let uu____8539 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b in
                                              let uu____8546 =
                                                let uu____8555 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a in
                                                let uu____8562 =
                                                  let uu____8571 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b in
                                                  [uu____8571] in
                                                uu____8555 :: uu____8562 in
                                              uu____8539 :: uu____8546 in
                                            uu____8523 :: uu____8530 in
                                          uu____8507 :: uu____8514 in
                                        let uu____8614 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b in
                                        FStar_Syntax_Util.arrow uu____8498
                                          uu____8614 in
                                      let uu____8617 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____8617
                                        (FStar_Pervasives_Native.Some k)) in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____8631 = fresh_a_and_wp () in
                              match uu____8631 with
                              | (a, wp_sort_a) ->
                                  let uu____8644 =
                                    FStar_Syntax_Util.type_u () in
                                  (match uu____8644 with
                                   | (t, uu____8650) ->
                                       let k =
                                         let uu____8654 =
                                           let uu____8663 =
                                             FStar_Syntax_Syntax.mk_binder a in
                                           let uu____8670 =
                                             let uu____8679 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             let uu____8686 =
                                               let uu____8695 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a in
                                               [uu____8695] in
                                             uu____8679 :: uu____8686 in
                                           uu____8663 :: uu____8670 in
                                         let uu____8726 =
                                           FStar_Syntax_Syntax.mk_Total t in
                                         FStar_Syntax_Util.arrow uu____8654
                                           uu____8726 in
                                       let uu____8729 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____8729
                                         (FStar_Pervasives_Native.Some k)) in
                            log_combinator "stronger" stronger;
                            (let if_then_else =
                               let uu____8743 = fresh_a_and_wp () in
                               match uu____8743 with
                               | (a, wp_sort_a) ->
                                   let p =
                                     let uu____8757 =
                                       let uu____8760 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname in
                                       FStar_Pervasives_Native.Some
                                         uu____8760 in
                                     let uu____8761 =
                                       let uu____8762 =
                                         FStar_Syntax_Util.type_u () in
                                       FStar_All.pipe_right uu____8762
                                         FStar_Pervasives_Native.fst in
                                     FStar_Syntax_Syntax.new_bv uu____8757
                                       uu____8761 in
                                   let k =
                                     let uu____8774 =
                                       let uu____8783 =
                                         FStar_Syntax_Syntax.mk_binder a in
                                       let uu____8790 =
                                         let uu____8799 =
                                           FStar_Syntax_Syntax.mk_binder p in
                                         let uu____8806 =
                                           let uu____8815 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a in
                                           let uu____8822 =
                                             let uu____8831 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a in
                                             [uu____8831] in
                                           uu____8815 :: uu____8822 in
                                         uu____8799 :: uu____8806 in
                                       uu____8783 :: uu____8790 in
                                     let uu____8868 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a in
                                     FStar_Syntax_Util.arrow uu____8774
                                       uu____8868 in
                                   let uu____8871 =
                                     let uu____8876 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator in
                                     FStar_All.pipe_right uu____8876
                                       FStar_Util.must in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____8871
                                     (FStar_Pervasives_Native.Some k) in
                             log_combinator "if_then_else" if_then_else;
                             (let ite_wp =
                                let uu____8908 = fresh_a_and_wp () in
                                match uu____8908 with
                                | (a, wp_sort_a) ->
                                    let k =
                                      let uu____8924 =
                                        let uu____8933 =
                                          FStar_Syntax_Syntax.mk_binder a in
                                        let uu____8940 =
                                          let uu____8949 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a in
                                          [uu____8949] in
                                        uu____8933 :: uu____8940 in
                                      let uu____8974 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a in
                                      FStar_Syntax_Util.arrow uu____8924
                                        uu____8974 in
                                    let uu____8977 =
                                      let uu____8982 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator in
                                      FStar_All.pipe_right uu____8982
                                        FStar_Util.must in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____8977
                                      (FStar_Pervasives_Native.Some k) in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____8998 = fresh_a_and_wp () in
                                 match uu____8998 with
                                 | (a, wp_sort_a) ->
                                     let b =
                                       let uu____9012 =
                                         let uu____9015 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname in
                                         FStar_Pervasives_Native.Some
                                           uu____9015 in
                                       let uu____9016 =
                                         let uu____9017 =
                                           FStar_Syntax_Util.type_u () in
                                         FStar_All.pipe_right uu____9017
                                           FStar_Pervasives_Native.fst in
                                       FStar_Syntax_Syntax.new_bv uu____9012
                                         uu____9016 in
                                     let wp_sort_b_a =
                                       let uu____9029 =
                                         let uu____9038 =
                                           let uu____9045 =
                                             FStar_Syntax_Syntax.bv_to_name b in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____9045 in
                                         [uu____9038] in
                                       let uu____9058 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____9029
                                         uu____9058 in
                                     let k =
                                       let uu____9064 =
                                         let uu____9073 =
                                           FStar_Syntax_Syntax.mk_binder a in
                                         let uu____9080 =
                                           let uu____9089 =
                                             FStar_Syntax_Syntax.mk_binder b in
                                           let uu____9096 =
                                             let uu____9105 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a in
                                             [uu____9105] in
                                           uu____9089 :: uu____9096 in
                                         uu____9073 :: uu____9080 in
                                       let uu____9136 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a in
                                       FStar_Syntax_Util.arrow uu____9064
                                         uu____9136 in
                                     let uu____9139 =
                                       let uu____9144 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator in
                                       FStar_All.pipe_right uu____9144
                                         FStar_Util.must in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____9139
                                       (FStar_Pervasives_Native.Some k) in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____9160 = fresh_a_and_wp () in
                                  match uu____9160 with
                                  | (a, wp_sort_a) ->
                                      let uu____9173 =
                                        FStar_Syntax_Util.type_u () in
                                      (match uu____9173 with
                                       | (t, uu____9179) ->
                                           let k =
                                             let uu____9183 =
                                               let uu____9192 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a in
                                               let uu____9199 =
                                                 let uu____9208 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a in
                                                 [uu____9208] in
                                               uu____9192 :: uu____9199 in
                                             let uu____9233 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t in
                                             FStar_Syntax_Util.arrow
                                               uu____9183 uu____9233 in
                                           let trivial =
                                             let uu____9237 =
                                               let uu____9242 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator in
                                               FStar_All.pipe_right
                                                 uu____9242 FStar_Util.must in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____9237
                                               (FStar_Pervasives_Native.Some
                                                  k) in
                                           (log_combinator "trivial" trivial;
                                            trivial)) in
                                let uu____9257 =
                                  let uu____9274 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr in
                                  match uu____9274 with
                                  | FStar_Pervasives_Native.None ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____9303 ->
                                      let repr =
                                        let uu____9307 = fresh_a_and_wp () in
                                        match uu____9307 with
                                        | (a, wp_sort_a) ->
                                            let uu____9320 =
                                              FStar_Syntax_Util.type_u () in
                                            (match uu____9320 with
                                             | (t, uu____9326) ->
                                                 let k =
                                                   let uu____9330 =
                                                     let uu____9339 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a in
                                                     let uu____9346 =
                                                       let uu____9355 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a in
                                                       [uu____9355] in
                                                     uu____9339 :: uu____9346 in
                                                   let uu____9380 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t in
                                                   FStar_Syntax_Util.arrow
                                                     uu____9330 uu____9380 in
                                                 let uu____9383 =
                                                   let uu____9388 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr in
                                                   FStar_All.pipe_right
                                                     uu____9388
                                                     FStar_Util.must in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____9383
                                                   (FStar_Pervasives_Native.Some
                                                      k)) in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____9432 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr in
                                          match uu____9432 with
                                          | (uu____9439, repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1 in
                                              let uu____9442 =
                                                let uu____9443 =
                                                  let uu____9460 =
                                                    let uu____9471 =
                                                      FStar_All.pipe_right t
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____9488 =
                                                      let uu____9499 =
                                                        FStar_All.pipe_right
                                                          wp
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____9499] in
                                                    uu____9471 :: uu____9488 in
                                                  (repr2, uu____9460) in
                                                FStar_Syntax_Syntax.Tm_app
                                                  uu____9443 in
                                              FStar_Syntax_Syntax.mk
                                                uu____9442
                                                FStar_Range.dummyRange in
                                        let mk_repr a wp =
                                          let uu____9565 =
                                            FStar_Syntax_Syntax.bv_to_name a in
                                          mk_repr' uu____9565 wp in
                                        let destruct_repr t =
                                          let uu____9580 =
                                            let uu____9581 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____9581.FStar_Syntax_Syntax.n in
                                          match uu____9580 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____9592,
                                               (t1, uu____9594)::(wp,
                                                                  uu____9596)::[])
                                              -> (t1, wp)
                                          | uu____9655 ->
                                              failwith "Unexpected repr type" in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____9671 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr in
                                            FStar_All.pipe_right uu____9671
                                              FStar_Util.must in
                                          let uu____9698 = fresh_a_and_wp () in
                                          match uu____9698 with
                                          | (a, uu____9706) ->
                                              let x_a =
                                                let uu____9712 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____9712 in
                                              let res =
                                                let wp =
                                                  let uu____9718 =
                                                    let uu____9719 =
                                                      FStar_TypeChecker_Env.inst_tscheme
                                                        ret_wp in
                                                    FStar_All.pipe_right
                                                      uu____9719
                                                      FStar_Pervasives_Native.snd in
                                                  let uu____9728 =
                                                    let uu____9729 =
                                                      let uu____9738 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_All.pipe_right
                                                        uu____9738
                                                        FStar_Syntax_Syntax.as_arg in
                                                    let uu____9747 =
                                                      let uu____9758 =
                                                        let uu____9767 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            x_a in
                                                        FStar_All.pipe_right
                                                          uu____9767
                                                          FStar_Syntax_Syntax.as_arg in
                                                      [uu____9758] in
                                                    uu____9729 :: uu____9747 in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    uu____9718 uu____9728
                                                    FStar_Range.dummyRange in
                                                mk_repr a wp in
                                              let k =
                                                let uu____9803 =
                                                  let uu____9812 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a in
                                                  let uu____9819 =
                                                    let uu____9828 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a in
                                                    [uu____9828] in
                                                  uu____9812 :: uu____9819 in
                                                let uu____9853 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res in
                                                FStar_Syntax_Util.arrow
                                                  uu____9803 uu____9853 in
                                              let uu____9856 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k in
                                              (match uu____9856 with
                                               | (k1, uu____9864, uu____9865)
                                                   ->
                                                   let env1 =
                                                     let uu____9869 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos in
                                                     FStar_Pervasives_Native.Some
                                                       uu____9869 in
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
                                             let uu____9882 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr in
                                             FStar_All.pipe_right uu____9882
                                               FStar_Util.must in
                                           let r =
                                             let uu____9920 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None in
                                             FStar_All.pipe_right uu____9920
                                               FStar_Syntax_Syntax.fv_to_tm in
                                           let uu____9921 = fresh_a_and_wp () in
                                           match uu____9921 with
                                           | (a, wp_sort_a) ->
                                               let uu____9934 =
                                                 fresh_a_and_wp () in
                                               (match uu____9934 with
                                                | (b, wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____9950 =
                                                        let uu____9959 =
                                                          let uu____9966 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____9966 in
                                                        [uu____9959] in
                                                      let uu____9979 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b in
                                                      FStar_Syntax_Util.arrow
                                                        uu____9950 uu____9979 in
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
                                                      let uu____9987 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____9987 in
                                                    let wp_g_x =
                                                      let uu____9990 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          wp_g in
                                                      let uu____9991 =
                                                        let uu____9992 =
                                                          let uu____10001 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a in
                                                          FStar_All.pipe_right
                                                            uu____10001
                                                            FStar_Syntax_Syntax.as_arg in
                                                        [uu____9992] in
                                                      FStar_Syntax_Syntax.mk_Tm_app
                                                        uu____9990 uu____9991
                                                        FStar_Range.dummyRange in
                                                    let res =
                                                      let wp =
                                                        let uu____10030 =
                                                          let uu____10031 =
                                                            FStar_TypeChecker_Env.inst_tscheme
                                                              bind_wp in
                                                          FStar_All.pipe_right
                                                            uu____10031
                                                            FStar_Pervasives_Native.snd in
                                                        let uu____10040 =
                                                          let uu____10041 =
                                                            let uu____10044 =
                                                              let uu____10047
                                                                =
                                                                FStar_Syntax_Syntax.bv_to_name
                                                                  a in
                                                              let uu____10048
                                                                =
                                                                let uu____10051
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                let uu____10052
                                                                  =
                                                                  let uu____10055
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  let uu____10056
                                                                    =
                                                                    let uu____10059
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g in
                                                                    [uu____10059] in
                                                                  uu____10055
                                                                    ::
                                                                    uu____10056 in
                                                                uu____10051
                                                                  ::
                                                                  uu____10052 in
                                                              uu____10047 ::
                                                                uu____10048 in
                                                            r :: uu____10044 in
                                                          FStar_List.map
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10041 in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____10030
                                                          uu____10040
                                                          FStar_Range.dummyRange in
                                                      mk_repr b wp in
                                                    let maybe_range_arg =
                                                      let uu____10077 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs in
                                                      if uu____10077
                                                      then
                                                        let uu____10088 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range in
                                                        let uu____10095 =
                                                          let uu____10104 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range in
                                                          [uu____10104] in
                                                        uu____10088 ::
                                                          uu____10095
                                                      else [] in
                                                    let k =
                                                      let uu____10140 =
                                                        let uu____10149 =
                                                          let uu____10158 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a in
                                                          let uu____10165 =
                                                            let uu____10174 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b in
                                                            [uu____10174] in
                                                          uu____10158 ::
                                                            uu____10165 in
                                                        let uu____10199 =
                                                          let uu____10208 =
                                                            let uu____10217 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f in
                                                            let uu____10224 =
                                                              let uu____10233
                                                                =
                                                                let uu____10240
                                                                  =
                                                                  let uu____10241
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f in
                                                                  mk_repr a
                                                                    uu____10241 in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____10240 in
                                                              let uu____10242
                                                                =
                                                                let uu____10251
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g in
                                                                let uu____10258
                                                                  =
                                                                  let uu____10267
                                                                    =
                                                                    let uu____10274
                                                                    =
                                                                    let uu____10275
                                                                    =
                                                                    let uu____10284
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a in
                                                                    [uu____10284] in
                                                                    let uu____10303
                                                                    =
                                                                    let uu____10306
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____10306 in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____10275
                                                                    uu____10303 in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____10274 in
                                                                  [uu____10267] in
                                                                uu____10251
                                                                  ::
                                                                  uu____10258 in
                                                              uu____10233 ::
                                                                uu____10242 in
                                                            uu____10217 ::
                                                              uu____10224 in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____10208 in
                                                        FStar_List.append
                                                          uu____10149
                                                          uu____10199 in
                                                      let uu____10351 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res in
                                                      FStar_Syntax_Util.arrow
                                                        uu____10140
                                                        uu____10351 in
                                                    let uu____10354 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k in
                                                    (match uu____10354 with
                                                     | (k1, uu____10362,
                                                        uu____10363) ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___978_10373
                                                                = env1 in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.erasable_types_tab);
                                                                FStar_TypeChecker_Env.enable_defer_to_tac
                                                                  =
                                                                  (uu___978_10373.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                              })
                                                             (fun uu____10375
                                                                ->
                                                                FStar_Pervasives_Native.Some
                                                                  uu____10375) in
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
                                              (let uu____10402 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____10416 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs in
                                                    match uu____10416 with
                                                    | (usubst, uvs) ->
                                                        let uu____10439 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs in
                                                        let uu____10440 =
                                                          let uu___991_10441
                                                            = act in
                                                          let uu____10442 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn in
                                                          let uu____10443 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___991_10441.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___991_10441.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___991_10441.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____10442;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____10443
                                                          } in
                                                        (uu____10439,
                                                          uu____10440)) in
                                               match uu____10402 with
                                               | (env1, act1) ->
                                                   let act_typ =
                                                     let uu____10447 =
                                                       let uu____10448 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ in
                                                       uu____10448.FStar_Syntax_Syntax.n in
                                                     match uu____10447 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1, c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c in
                                                         let uu____10474 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname in
                                                         if uu____10474
                                                         then
                                                           let uu____10477 =
                                                             let uu____10480
                                                               =
                                                               let uu____10481
                                                                 =
                                                                 let uu____10482
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____10482 in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____10481 in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____10480 in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____10477
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____10505 ->
                                                         act1.FStar_Syntax_Syntax.action_typ in
                                                   let uu____10506 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ in
                                                   (match uu____10506 with
                                                    | (act_typ1, uu____10514,
                                                       g_t) ->
                                                        let env' =
                                                          let uu___1008_10517
                                                            =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1 in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.try_solve_implicits_hook
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.erasable_types_tab);
                                                            FStar_TypeChecker_Env.enable_defer_to_tac
                                                              =
                                                              (uu___1008_10517.FStar_TypeChecker_Env.enable_defer_to_tac)
                                                          } in
                                                        ((let uu____10520 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED") in
                                                          if uu____10520
                                                          then
                                                            let uu____10524 =
                                                              FStar_Ident.string_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name in
                                                            let uu____10526 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn in
                                                            let uu____10528 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1 in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____10524
                                                              uu____10526
                                                              uu____10528
                                                          else ());
                                                         (let uu____10533 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn in
                                                          match uu____10533
                                                          with
                                                          | (act_defn,
                                                             uu____10541,
                                                             g_a) ->
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
                                                              let uu____10545
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
                                                                    let uu____10581
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10581
                                                                    with
                                                                    | 
                                                                    (bs2,
                                                                    uu____10593)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun in
                                                                    let k =
                                                                    let uu____10600
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10600 in
                                                                    let uu____10603
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k in
                                                                    (match uu____10603
                                                                    with
                                                                    | 
                                                                    (k1,
                                                                    uu____10617,
                                                                    g) ->
                                                                    (k1, g)))
                                                                | uu____10621
                                                                    ->
                                                                    let uu____10622
                                                                    =
                                                                    let uu____10628
                                                                    =
                                                                    let uu____10630
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3 in
                                                                    let uu____10632
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3 in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____10630
                                                                    uu____10632 in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____10628) in
                                                                    FStar_Errors.raise_error
                                                                    uu____10622
                                                                    act_defn1.FStar_Syntax_Syntax.pos in
                                                              (match uu____10545
                                                               with
                                                               | (expected_k,
                                                                  g_k) ->
                                                                   let g =
                                                                    FStar_TypeChecker_Rel.teq
                                                                    env1
                                                                    act_typ2
                                                                    expected_k in
                                                                   ((
                                                                    let uu____10650
                                                                    =
                                                                    let uu____10651
                                                                    =
                                                                    let uu____10652
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____10652 in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____10651 in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____10650);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____10654
                                                                    =
                                                                    let uu____10655
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k in
                                                                    uu____10655.FStar_Syntax_Syntax.n in
                                                                    match uu____10654
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1, c)
                                                                    ->
                                                                    let uu____10680
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c in
                                                                    (match uu____10680
                                                                    with
                                                                    | 
                                                                    (bs2, c1)
                                                                    ->
                                                                    let uu____10687
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1) in
                                                                    (match uu____10687
                                                                    with
                                                                    | 
                                                                    (a, wp)
                                                                    ->
                                                                    let c2 =
                                                                    let uu____10707
                                                                    =
                                                                    let uu____10708
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a in
                                                                    [uu____10708] in
                                                                    let uu____10709
                                                                    =
                                                                    let uu____10720
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp in
                                                                    [uu____10720] in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____10707;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____10709;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    } in
                                                                    let uu____10745
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____10745))
                                                                    | 
                                                                    uu____10748
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)" in
                                                                    let uu____10750
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____10772
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1 in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____10772)) in
                                                                    match uu____10750
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
                                                                    let uu___1058_10791
                                                                    = act1 in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___1058_10791.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___1058_10791.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___1058_10791.FStar_Syntax_Syntax.action_params);
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
                                match uu____9257 with
                                | (repr, return_repr, bind_repr, actions) ->
                                    let cl ts =
                                      let ts1 =
                                        FStar_Syntax_Subst.close_tscheme
                                          ed_bs ts in
                                      let ed_univs_closing =
                                        FStar_Syntax_Subst.univ_var_closing
                                          ed_univs in
                                      let uu____10834 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____10834 ts1 in
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
                                          uu____10846 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____10847 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____10848 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected" in
                                    let ed3 =
                                      let uu___1078_10851 = ed2 in
                                      let uu____10852 = cl signature in
                                      let uu____10853 =
                                        FStar_List.map
                                          (fun a ->
                                             let uu___1081_10861 = a in
                                             let uu____10862 =
                                               let uu____10863 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn)) in
                                               FStar_All.pipe_right
                                                 uu____10863
                                                 FStar_Pervasives_Native.snd in
                                             let uu____10888 =
                                               let uu____10889 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ)) in
                                               FStar_All.pipe_right
                                                 uu____10889
                                                 FStar_Pervasives_Native.snd in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___1081_10861.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___1081_10861.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___1081_10861.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___1081_10861.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____10862;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____10888
                                             }) actions in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___1078_10851.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___1078_10851.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___1078_10851.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___1078_10851.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____10852;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____10853;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___1078_10851.FStar_Syntax_Syntax.eff_attrs)
                                      } in
                                    ((let uu____10915 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED") in
                                      if uu____10915
                                      then
                                        let uu____10920 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3 in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____10920
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
        let uu____10946 =
          let uu____10961 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered in
          if uu____10961
          then tc_layered_eff_decl
          else tc_non_layered_eff_decl in
        uu____10946 env ed quals
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
        let fail uu____11011 =
          let uu____11012 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s in
          let uu____11018 = FStar_Ident.range_of_lid m in
          FStar_Errors.raise_error uu____11012 uu____11018 in
        let s1 = FStar_Syntax_Subst.compress s in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs in
            (match bs1 with
             | (a, uu____11062)::(wp, uu____11064)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____11093 -> fail ())
        | uu____11094 -> fail ()
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0 ->
    fun sub ->
      (let uu____11107 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffectsTc") in
       if uu____11107
       then
         let uu____11112 = FStar_Syntax_Print.sub_eff_to_string sub in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____11112
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub.FStar_Syntax_Syntax.lift FStar_Util.must in
       let r =
         let uu____11129 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd in
         uu____11129.FStar_Syntax_Syntax.pos in
       let uu____11138 = check_and_gen env0 "" "lift" Prims.int_one lift_ts in
       match uu____11138 with
       | (us, lift, lift_ty) ->
           ((let uu____11152 =
               FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                 (FStar_Options.Other "LayeredEffectsTc") in
             if uu____11152
             then
               let uu____11157 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift) in
               let uu____11163 =
                 FStar_Syntax_Print.tscheme_to_string (us, lift_ty) in
               FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                 uu____11157 uu____11163
             else ());
            (let uu____11172 = FStar_Syntax_Subst.open_univ_vars us lift_ty in
             match uu____11172 with
             | (us1, lift_ty1) ->
                 let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                 (check_no_subtyping_for_layered_combinator env lift_ty1
                    FStar_Pervasives_Native.None;
                  (let lift_t_shape_error s =
                     let uu____11190 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.source in
                     let uu____11192 =
                       FStar_Ident.string_of_lid
                         sub.FStar_Syntax_Syntax.target in
                     let uu____11194 =
                       FStar_Syntax_Print.term_to_string lift_ty1 in
                     FStar_Util.format4
                       "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                       uu____11190 uu____11192 s uu____11194 in
                   let uu____11197 =
                     let uu____11204 =
                       let uu____11209 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____11209
                         (fun uu____11226 ->
                            match uu____11226 with
                            | (t, u) ->
                                let uu____11237 =
                                  let uu____11238 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t in
                                  FStar_All.pipe_right uu____11238
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____11237, u)) in
                     match uu____11204 with
                     | (a, u_a) ->
                         let rest_bs =
                           let uu____11257 =
                             let uu____11258 =
                               FStar_Syntax_Subst.compress lift_ty1 in
                             uu____11258.FStar_Syntax_Syntax.n in
                           match uu____11257 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____11270)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____11298 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____11298 with
                                | (a', uu____11308)::bs1 ->
                                    let uu____11328 =
                                      let uu____11329 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____11329
                                        FStar_Pervasives_Native.fst in
                                    let uu____11395 =
                                      let uu____11408 =
                                        let uu____11411 =
                                          let uu____11412 =
                                            let uu____11419 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____11419) in
                                          FStar_Syntax_Syntax.NT uu____11412 in
                                        [uu____11411] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____11408 in
                                    FStar_All.pipe_right uu____11328
                                      uu____11395)
                           | uu____11434 ->
                               let uu____11435 =
                                 let uu____11441 =
                                   lift_t_shape_error
                                     "either not an arrow, or not enough binders" in
                                 (FStar_Errors.Fatal_UnexpectedExpressionType,
                                   uu____11441) in
                               FStar_Errors.raise_error uu____11435 r in
                         let uu____11453 =
                           let uu____11464 =
                             let uu____11469 =
                               FStar_TypeChecker_Env.push_binders env (a ::
                                 rest_bs) in
                             let uu____11476 =
                               let uu____11477 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____11477
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____11469 r sub.FStar_Syntax_Syntax.source
                               u_a uu____11476 in
                           match uu____11464 with
                           | (f_sort, g) ->
                               let uu____11498 =
                                 let uu____11505 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None f_sort in
                                 FStar_All.pipe_right uu____11505
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____11498, g) in
                         (match uu____11453 with
                          | (f_b, g_f_b) ->
                              let bs = a :: (FStar_List.append rest_bs [f_b]) in
                              let uu____11572 =
                                let uu____11577 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____11578 =
                                  let uu____11579 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____11579
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____11577 r
                                  sub.FStar_Syntax_Syntax.target u_a
                                  uu____11578 in
                              (match uu____11572 with
                               | (repr, g_repr) ->
                                   let uu____11596 =
                                     let uu____11601 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____11602 =
                                       let uu____11604 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.source in
                                       let uu____11606 =
                                         FStar_Ident.string_of_lid
                                           sub.FStar_Syntax_Syntax.target in
                                       FStar_Util.format2
                                         "implicit for pure_wp in typechecking lift %s~>%s"
                                         uu____11604 uu____11606 in
                                     pure_wp_uvar uu____11601 repr
                                       uu____11602 r in
                                   (match uu____11596 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____11618 =
                                            let uu____11619 =
                                              let uu____11620 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____11620] in
                                            let uu____11621 =
                                              let uu____11632 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____11632] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____11619;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = repr;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____11621;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____11618 in
                                        let uu____11665 =
                                          FStar_Syntax_Util.arrow bs c in
                                        let uu____11668 =
                                          let uu____11669 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_f_b g_repr in
                                          FStar_TypeChecker_Env.conj_guard
                                            uu____11669 guard_wp in
                                        (uu____11665, uu____11668)))) in
                   match uu____11197 with
                   | (k, g_k) ->
                       ((let uu____11679 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffectsTc") in
                         if uu____11679
                         then
                           let uu____11684 =
                             FStar_Syntax_Print.term_to_string k in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____11684
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____11693 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffectsTc") in
                          if uu____11693
                          then
                            let uu____11698 =
                              FStar_Syntax_Print.term_to_string k in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____11698
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env) in
                          (let uu____11705 =
                             let uu____11706 = FStar_Syntax_Subst.compress k1 in
                             uu____11706.FStar_Syntax_Syntax.n in
                           match uu____11705 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
                               let uu____11731 =
                                 FStar_Syntax_Subst.open_comp bs c in
                               (match uu____11731 with
                                | (bs1, c1) ->
                                    let res_t =
                                      FStar_Syntax_Util.comp_result c1 in
                                    let uu____11741 =
                                      let uu____11760 =
                                        FStar_List.splitAt
                                          ((FStar_List.length bs1) -
                                             Prims.int_one) bs1 in
                                      FStar_All.pipe_right uu____11760
                                        (fun uu____11837 ->
                                           match uu____11837 with
                                           | (l1, l2) ->
                                               let uu____11910 =
                                                 FStar_List.tl l1 in
                                               let uu____11925 =
                                                 FStar_List.hd l2 in
                                               (uu____11910, uu____11925)) in
                                    (match uu____11741 with
                                     | (bs2, f_b) ->
                                         validate_layered_effect_binders env
                                           bs2
                                           [(FStar_Pervasives_Native.fst f_b).FStar_Syntax_Syntax.sort;
                                           res_t] r)));
                          (let sub1 =
                             let uu___1186_11985 = sub in
                             let uu____11986 =
                               let uu____11989 =
                                 let uu____11990 =
                                   FStar_All.pipe_right k1
                                     (FStar_Syntax_Subst.close_univ_vars us1) in
                                 (us1, uu____11990) in
                               FStar_Pervasives_Native.Some uu____11989 in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1186_11985.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1186_11985.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____11986;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             } in
                           (let uu____12004 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffectsTc") in
                            if uu____12004
                            then
                              let uu____12009 =
                                FStar_Syntax_Print.sub_eff_to_string sub1 in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____12009
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
          let uu____12046 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k in
          FStar_TypeChecker_Util.generalize_universes env1 uu____12046 in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.source in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub.FStar_Syntax_Syntax.target in
        let uu____12049 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered) in
        if uu____12049
        then tc_layered_lift env sub
        else
          (let uu____12056 =
             let uu____12063 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub.FStar_Syntax_Syntax.source in
             monad_signature env sub.FStar_Syntax_Syntax.source uu____12063 in
           match uu____12056 with
           | (a, wp_a_src) ->
               let uu____12070 =
                 let uu____12077 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub.FStar_Syntax_Syntax.target in
                 monad_signature env sub.FStar_Syntax_Syntax.target
                   uu____12077 in
               (match uu____12070 with
                | (b, wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____12085 =
                        let uu____12088 =
                          let uu____12089 =
                            let uu____12096 =
                              FStar_Syntax_Syntax.bv_to_name a in
                            (b, uu____12096) in
                          FStar_Syntax_Syntax.NT uu____12089 in
                        [uu____12088] in
                      FStar_Syntax_Subst.subst uu____12085 wp_b_tgt in
                    let expected_k =
                      let uu____12104 =
                        let uu____12113 = FStar_Syntax_Syntax.mk_binder a in
                        let uu____12120 =
                          let uu____12129 =
                            FStar_Syntax_Syntax.null_binder wp_a_src in
                          [uu____12129] in
                        uu____12113 :: uu____12120 in
                      let uu____12154 = FStar_Syntax_Syntax.mk_Total wp_a_tgt in
                      FStar_Syntax_Util.arrow uu____12104 uu____12154 in
                    let repr_type eff_name a1 wp =
                      (let uu____12176 =
                         let uu____12178 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name in
                         Prims.op_Negation uu____12178 in
                       if uu____12176
                       then
                         let uu____12181 =
                           let uu____12187 =
                             let uu____12189 =
                               FStar_Ident.string_of_lid eff_name in
                             FStar_Util.format1 "Effect %s cannot be reified"
                               uu____12189 in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____12187) in
                         let uu____12193 =
                           FStar_TypeChecker_Env.get_range env in
                         FStar_Errors.raise_error uu____12181 uu____12193
                       else ());
                      (let uu____12196 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name in
                       match uu____12196 with
                       | FStar_Pervasives_Native.None ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                           let repr =
                             let uu____12229 =
                               let uu____12230 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr in
                               FStar_All.pipe_right uu____12230
                                 FStar_Util.must in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____12229 in
                           let uu____12237 =
                             let uu____12238 =
                               let uu____12255 =
                                 let uu____12266 =
                                   FStar_Syntax_Syntax.as_arg a1 in
                                 let uu____12275 =
                                   let uu____12286 =
                                     FStar_Syntax_Syntax.as_arg wp in
                                   [uu____12286] in
                                 uu____12266 :: uu____12275 in
                               (repr, uu____12255) in
                             FStar_Syntax_Syntax.Tm_app uu____12238 in
                           let uu____12331 =
                             FStar_TypeChecker_Env.get_range env in
                           FStar_Syntax_Syntax.mk uu____12237 uu____12331) in
                    let uu____12332 =
                      match ((sub.FStar_Syntax_Syntax.lift),
                              (sub.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None,
                         FStar_Pervasives_Native.None) ->
                          failwith "Impossible (parser)"
                      | (lift, FStar_Pervasives_Native.Some (uvs, lift_wp))
                          ->
                          let uu____12505 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____12516 =
                                FStar_Syntax_Subst.univ_var_opening uvs in
                              match uu____12516 with
                              | (usubst, uvs1) ->
                                  let uu____12539 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1 in
                                  let uu____12540 =
                                    FStar_Syntax_Subst.subst usubst lift_wp in
                                  (uu____12539, uu____12540)
                            else (env, lift_wp) in
                          (match uu____12505 with
                           | (env1, lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k in
                                    let uu____12590 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2 in
                                    (uvs, uu____12590)) in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some (what, lift),
                         FStar_Pervasives_Native.None) ->
                          let uu____12661 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____12676 =
                                FStar_Syntax_Subst.univ_var_opening what in
                              match uu____12676 with
                              | (usubst, uvs) ->
                                  let uu____12701 =
                                    FStar_Syntax_Subst.subst usubst lift in
                                  (uvs, uu____12701)
                            else ([], lift) in
                          (match uu____12661 with
                           | (uvs, lift1) ->
                               ((let uu____12737 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED") in
                                 if uu____12737
                                 then
                                   let uu____12741 =
                                     FStar_Syntax_Print.term_to_string lift1 in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____12741
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange) in
                                 let uu____12747 =
                                   let uu____12754 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____12754 lift1 in
                                 match uu____12747 with
                                 | (lift2, comp, uu____12779) ->
                                     let uu____12780 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2 in
                                     (match uu____12780 with
                                      | (uu____12809, lift_wp, lift_elab) ->
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
                                            let uu____12841 =
                                              let uu____12852 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1 in
                                              FStar_Pervasives_Native.Some
                                                uu____12852 in
                                            let uu____12869 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1 in
                                            (uu____12841, uu____12869)
                                          else
                                            (let uu____12898 =
                                               let uu____12909 =
                                                 let uu____12918 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1 in
                                                 (uvs, uu____12918) in
                                               FStar_Pervasives_Native.Some
                                                 uu____12909 in
                                             let uu____12933 =
                                               let uu____12942 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1 in
                                               (uvs, uu____12942) in
                                             (uu____12898, uu____12933)))))) in
                    (match uu____12332 with
                     | (lift, lift_wp) ->
                         let env1 =
                           let uu___1270_13006 = env in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1270_13006.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1270_13006.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1270_13006.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1270_13006.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1270_13006.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1270_13006.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1270_13006.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1270_13006.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1270_13006.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1270_13006.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1270_13006.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1270_13006.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1270_13006.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1270_13006.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1270_13006.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1270_13006.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1270_13006.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1270_13006.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1270_13006.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1270_13006.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1270_13006.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1270_13006.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1270_13006.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1270_13006.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1270_13006.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1270_13006.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1270_13006.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1270_13006.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1270_13006.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1270_13006.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1270_13006.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1270_13006.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1270_13006.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1270_13006.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1270_13006.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.try_solve_implicits_hook =
                               (uu___1270_13006.FStar_TypeChecker_Env.try_solve_implicits_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1270_13006.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1270_13006.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1270_13006.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1270_13006.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1270_13006.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1270_13006.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1270_13006.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1270_13006.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1270_13006.FStar_TypeChecker_Env.erasable_types_tab);
                             FStar_TypeChecker_Env.enable_defer_to_tac =
                               (uu___1270_13006.FStar_TypeChecker_Env.enable_defer_to_tac)
                           } in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs, lift1) ->
                               let uu____13039 =
                                 let uu____13044 =
                                   FStar_Syntax_Subst.univ_var_opening uvs in
                                 match uu____13044 with
                                 | (usubst, uvs1) ->
                                     let uu____13067 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1 in
                                     let uu____13068 =
                                       FStar_Syntax_Subst.subst usubst lift1 in
                                     (uu____13067, uu____13068) in
                               (match uu____13039 with
                                | (env2, lift2) ->
                                    let uu____13073 =
                                      let uu____13080 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2 sub.FStar_Syntax_Syntax.source in
                                      monad_signature env2
                                        sub.FStar_Syntax_Syntax.source
                                        uu____13080 in
                                    (match uu____13073 with
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
                                             let uu____13106 =
                                               let uu____13107 =
                                                 let uu____13124 =
                                                   let uu____13135 =
                                                     FStar_Syntax_Syntax.as_arg
                                                       a_typ in
                                                   let uu____13144 =
                                                     let uu____13155 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         wp_a_typ in
                                                     [uu____13155] in
                                                   uu____13135 :: uu____13144 in
                                                 (lift_wp1, uu____13124) in
                                               FStar_Syntax_Syntax.Tm_app
                                                 uu____13107 in
                                             let uu____13200 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2 in
                                             FStar_Syntax_Syntax.mk
                                               uu____13106 uu____13200 in
                                           repr_type
                                             sub.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a in
                                         let expected_k1 =
                                           let uu____13204 =
                                             let uu____13213 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1 in
                                             let uu____13220 =
                                               let uu____13229 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a in
                                               let uu____13236 =
                                                 let uu____13245 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f in
                                                 [uu____13245] in
                                               uu____13229 :: uu____13236 in
                                             uu____13213 :: uu____13220 in
                                           let uu____13276 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result in
                                           FStar_Syntax_Util.arrow
                                             uu____13204 uu____13276 in
                                         let uu____13279 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1 in
                                         (match uu____13279 with
                                          | (expected_k2, uu____13289,
                                             uu____13290) ->
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
                                                   let uu____13298 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3 in
                                                   (uvs, uu____13298)) in
                                              FStar_Pervasives_Native.Some
                                                lift3))) in
                         ((let uu____13306 =
                             let uu____13308 =
                               let uu____13310 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____13310
                                 FStar_List.length in
                             uu____13308 <> Prims.int_one in
                           if uu____13306
                           then
                             let uu____13333 =
                               let uu____13339 =
                                 let uu____13341 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____13343 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____13345 =
                                   let uu____13347 =
                                     let uu____13349 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____13349
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____13347
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____13341 uu____13343 uu____13345 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____13339) in
                             FStar_Errors.raise_error uu____13333 r
                           else ());
                          (let uu____13376 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____13379 =
                                  let uu____13381 =
                                    let uu____13384 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must in
                                    FStar_All.pipe_right uu____13384
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____13381
                                    FStar_List.length in
                                uu____13379 <> Prims.int_one) in
                           if uu____13376
                           then
                             let uu____13423 =
                               let uu____13429 =
                                 let uu____13431 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.source in
                                 let uu____13433 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub.FStar_Syntax_Syntax.target in
                                 let uu____13435 =
                                   let uu____13437 =
                                     let uu____13439 =
                                       let uu____13442 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must in
                                       FStar_All.pipe_right uu____13442
                                         FStar_Pervasives_Native.fst in
                                     FStar_All.pipe_right uu____13439
                                       FStar_List.length in
                                   FStar_All.pipe_right uu____13437
                                     FStar_Util.string_of_int in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____13431 uu____13433 uu____13435 in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____13429) in
                             FStar_Errors.raise_error uu____13423 r
                           else ());
                          (let uu___1307_13484 = sub in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1307_13484.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1307_13484.FStar_Syntax_Syntax.target);
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
    fun uu____13515 ->
      fun r ->
        match uu____13515 with
        | (lid, uvs, tps, c) ->
            let env0 = env in
            let uu____13538 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____13566 = FStar_Syntax_Subst.univ_var_opening uvs in
                 match uu____13566 with
                 | (usubst, uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps in
                     let c1 =
                       let uu____13597 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst in
                       FStar_Syntax_Subst.subst_comp uu____13597 c in
                     let uu____13606 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1 in
                     (uu____13606, uvs1, tps1, c1)) in
            (match uu____13538 with
             | (env1, uvs1, tps1, c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r in
                 let uu____13626 = FStar_Syntax_Subst.open_comp tps1 c1 in
                 (match uu____13626 with
                  | (tps2, c2) ->
                      let uu____13641 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2 in
                      (match uu____13641 with
                       | (tps3, env3, us) ->
                           let uu____13659 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2 in
                           (match uu____13659 with
                            | (c3, u, g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x, uu____13685)::uu____13686 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____13705 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3 in
                                  let uu____13713 =
                                    let uu____13715 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ in
                                    Prims.op_Negation uu____13715 in
                                  if uu____13713
                                  then
                                    let uu____13718 =
                                      let uu____13724 =
                                        let uu____13726 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ in
                                        let uu____13728 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____13726 uu____13728 in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____13724) in
                                    FStar_Errors.raise_error uu____13718 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3 in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3 in
                                  let uu____13736 =
                                    let uu____13737 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4)) r in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____13737 in
                                  match uu____13736 with
                                  | (uvs2, t) ->
                                      let uu____13766 =
                                        let uu____13771 =
                                          let uu____13784 =
                                            let uu____13785 =
                                              FStar_Syntax_Subst.compress t in
                                            uu____13785.FStar_Syntax_Syntax.n in
                                          (tps4, uu____13784) in
                                        match uu____13771 with
                                        | ([], FStar_Syntax_Syntax.Tm_arrow
                                           (uu____13800, c5)) -> ([], c5)
                                        | (uu____13842,
                                           FStar_Syntax_Syntax.Tm_arrow
                                           (tps5, c5)) -> (tps5, c5)
                                        | uu____13881 ->
                                            failwith
                                              "Impossible (t is an arrow)" in
                                      (match uu____13766 with
                                       | (tps5, c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____13913 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t in
                                               match uu____13913 with
                                               | (uu____13918, t1) ->
                                                   let uu____13920 =
                                                     let uu____13926 =
                                                       let uu____13928 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid in
                                                       let uu____13930 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int in
                                                       let uu____13934 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1 in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____13928
                                                         uu____13930
                                                         uu____13934 in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____13926) in
                                                   FStar_Errors.raise_error
                                                     uu____13920 r)
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
              let uu____13976 =
                let uu____13978 =
                  FStar_All.pipe_right m FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13978 FStar_Ident.string_of_id in
              let uu____13980 =
                let uu____13982 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13982 FStar_Ident.string_of_id in
              let uu____13984 =
                let uu____13986 =
                  FStar_All.pipe_right p FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____13986 FStar_Ident.string_of_id in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____13976 uu____13980
                uu____13984 in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos in
            let uu____13994 =
              check_and_gen env eff_name "polymonadic_bind"
                (Prims.of_int (2)) ts in
            match uu____13994 with
            | (us, t, ty) ->
                let uu____14010 = FStar_Syntax_Subst.open_univ_vars us ty in
                (match uu____14010 with
                 | (us1, ty1) ->
                     let env1 = FStar_TypeChecker_Env.push_univ_vars env us1 in
                     (check_no_subtyping_for_layered_combinator env1 ty1
                        FStar_Pervasives_Native.None;
                      (let uu____14023 =
                         let uu____14028 = FStar_Syntax_Util.type_u () in
                         FStar_All.pipe_right uu____14028
                           (fun uu____14045 ->
                              match uu____14045 with
                              | (t1, u) ->
                                  let uu____14056 =
                                    let uu____14057 =
                                      FStar_Syntax_Syntax.gen_bv "a"
                                        FStar_Pervasives_Native.None t1 in
                                    FStar_All.pipe_right uu____14057
                                      FStar_Syntax_Syntax.mk_binder in
                                  (uu____14056, u)) in
                       match uu____14023 with
                       | (a, u_a) ->
                           let uu____14065 =
                             let uu____14070 = FStar_Syntax_Util.type_u () in
                             FStar_All.pipe_right uu____14070
                               (fun uu____14087 ->
                                  match uu____14087 with
                                  | (t1, u) ->
                                      let uu____14098 =
                                        let uu____14099 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1 in
                                        FStar_All.pipe_right uu____14099
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____14098, u)) in
                           (match uu____14065 with
                            | (b, u_b) ->
                                let rest_bs =
                                  let uu____14116 =
                                    let uu____14117 =
                                      FStar_Syntax_Subst.compress ty1 in
                                    uu____14117.FStar_Syntax_Syntax.n in
                                  match uu____14116 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs, uu____14129) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____14157 =
                                        FStar_Syntax_Subst.open_binders bs in
                                      (match uu____14157 with
                                       | (a', uu____14167)::(b', uu____14169)::bs1
                                           ->
                                           let uu____14199 =
                                             let uu____14200 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2)))) in
                                             FStar_All.pipe_right uu____14200
                                               FStar_Pervasives_Native.fst in
                                           let uu____14266 =
                                             let uu____14279 =
                                               let uu____14282 =
                                                 let uu____14283 =
                                                   let uu____14290 =
                                                     let uu____14293 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst in
                                                     FStar_All.pipe_right
                                                       uu____14293
                                                       FStar_Syntax_Syntax.bv_to_name in
                                                   (a', uu____14290) in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____14283 in
                                               let uu____14306 =
                                                 let uu____14309 =
                                                   let uu____14310 =
                                                     let uu____14317 =
                                                       let uu____14320 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst in
                                                       FStar_All.pipe_right
                                                         uu____14320
                                                         FStar_Syntax_Syntax.bv_to_name in
                                                     (b', uu____14317) in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____14310 in
                                                 [uu____14309] in
                                               uu____14282 :: uu____14306 in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____14279 in
                                           FStar_All.pipe_right uu____14199
                                             uu____14266)
                                  | uu____14341 ->
                                      let uu____14342 =
                                        let uu____14348 =
                                          let uu____14350 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1 in
                                          let uu____14352 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1 in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____14350 uu____14352 in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____14348) in
                                      FStar_Errors.raise_error uu____14342 r in
                                let bs = a :: b :: rest_bs in
                                let uu____14385 =
                                  let uu____14396 =
                                    let uu____14401 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs in
                                    let uu____14402 =
                                      let uu____14403 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst in
                                      FStar_All.pipe_right uu____14403
                                        FStar_Syntax_Syntax.bv_to_name in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____14401 r m u_a uu____14402 in
                                  match uu____14396 with
                                  | (repr, g) ->
                                      let uu____14424 =
                                        let uu____14431 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr in
                                        FStar_All.pipe_right uu____14431
                                          FStar_Syntax_Syntax.mk_binder in
                                      (uu____14424, g) in
                                (match uu____14385 with
                                 | (f, guard_f) ->
                                     let uu____14463 =
                                       let x_a =
                                         let uu____14481 =
                                           let uu____14482 =
                                             let uu____14483 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst in
                                             FStar_All.pipe_right uu____14483
                                               FStar_Syntax_Syntax.bv_to_name in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____14482 in
                                         FStar_All.pipe_right uu____14481
                                           FStar_Syntax_Syntax.mk_binder in
                                       let uu____14499 =
                                         let uu____14504 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a]) in
                                         let uu____14523 =
                                           let uu____14524 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst in
                                           FStar_All.pipe_right uu____14524
                                             FStar_Syntax_Syntax.bv_to_name in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____14504 r n u_b uu____14523 in
                                       match uu____14499 with
                                       | (repr, g) ->
                                           let uu____14545 =
                                             let uu____14552 =
                                               let uu____14553 =
                                                 let uu____14554 =
                                                   let uu____14557 =
                                                     let uu____14560 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         () in
                                                     FStar_Pervasives_Native.Some
                                                       uu____14560 in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____14557 in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____14554 in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____14553 in
                                             FStar_All.pipe_right uu____14552
                                               FStar_Syntax_Syntax.mk_binder in
                                           (uu____14545, g) in
                                     (match uu____14463 with
                                      | (g, guard_g) ->
                                          let uu____14604 =
                                            let uu____14609 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs in
                                            let uu____14610 =
                                              let uu____14611 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst in
                                              FStar_All.pipe_right
                                                uu____14611
                                                FStar_Syntax_Syntax.bv_to_name in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____14609 r p u_b uu____14610 in
                                          (match uu____14604 with
                                           | (repr, guard_repr) ->
                                               let uu____14626 =
                                                 let uu____14631 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env1 bs in
                                                 let uu____14632 =
                                                   FStar_Util.format1
                                                     "implicit for pure_wp in checking %s"
                                                     eff_name in
                                                 pure_wp_uvar uu____14631
                                                   repr uu____14632 r in
                                               (match uu____14626 with
                                                | (pure_wp_uvar1,
                                                   g_pure_wp_uvar) ->
                                                    let k =
                                                      let uu____14644 =
                                                        let uu____14647 =
                                                          let uu____14648 =
                                                            let uu____14649 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                () in
                                                            [uu____14649] in
                                                          let uu____14650 =
                                                            let uu____14661 =
                                                              FStar_All.pipe_right
                                                                pure_wp_uvar1
                                                                FStar_Syntax_Syntax.as_arg in
                                                            [uu____14661] in
                                                          {
                                                            FStar_Syntax_Syntax.comp_univs
                                                              = uu____14648;
                                                            FStar_Syntax_Syntax.effect_name
                                                              =
                                                              FStar_Parser_Const.effect_PURE_lid;
                                                            FStar_Syntax_Syntax.result_typ
                                                              = repr;
                                                            FStar_Syntax_Syntax.effect_args
                                                              = uu____14650;
                                                            FStar_Syntax_Syntax.flags
                                                              = []
                                                          } in
                                                        FStar_Syntax_Syntax.mk_Comp
                                                          uu____14647 in
                                                      FStar_Syntax_Util.arrow
                                                        (FStar_List.append bs
                                                           [f; g])
                                                        uu____14644 in
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
                                                     (let uu____14721 =
                                                        FStar_All.pipe_left
                                                          (FStar_TypeChecker_Env.debug
                                                             env1)
                                                          FStar_Options.Extreme in
                                                      if uu____14721
                                                      then
                                                        let uu____14725 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, t) in
                                                        let uu____14731 =
                                                          FStar_Syntax_Print.tscheme_to_string
                                                            (us1, k) in
                                                        FStar_Util.print3
                                                          "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                          eff_name
                                                          uu____14725
                                                          uu____14731
                                                      else ());
                                                     (let k1 =
                                                        FStar_All.pipe_right
                                                          k
                                                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                             env1) in
                                                      (let uu____14742 =
                                                         let uu____14743 =
                                                           FStar_Syntax_Subst.compress
                                                             k1 in
                                                         uu____14743.FStar_Syntax_Syntax.n in
                                                       match uu____14742 with
                                                       | FStar_Syntax_Syntax.Tm_arrow
                                                           (bs1, c) ->
                                                           let uu____14768 =
                                                             FStar_Syntax_Subst.open_comp
                                                               bs1 c in
                                                           (match uu____14768
                                                            with
                                                            | (bs2, c1) ->
                                                                let res_t =
                                                                  FStar_Syntax_Util.comp_result
                                                                    c1 in
                                                                let uu____14778
                                                                  =
                                                                  let uu____14805
                                                                    =
                                                                    FStar_List.splitAt
                                                                    ((FStar_List.length
                                                                    bs2) -
                                                                    (Prims.of_int (2)))
                                                                    bs2 in
                                                                  FStar_All.pipe_right
                                                                    uu____14805
                                                                    (
                                                                    fun
                                                                    uu____14891
                                                                    ->
                                                                    match uu____14891
                                                                    with
                                                                    | 
                                                                    (l1, l2)
                                                                    ->
                                                                    let uu____14972
                                                                    =
                                                                    let uu____14981
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l1
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____14981
                                                                    FStar_List.tl in
                                                                    let uu____15034
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.hd in
                                                                    let uu____15061
                                                                    =
                                                                    let uu____15068
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    l2
                                                                    FStar_List.tl in
                                                                    FStar_All.pipe_right
                                                                    uu____15068
                                                                    FStar_List.hd in
                                                                    (uu____14972,
                                                                    uu____15034,
                                                                    uu____15061)) in
                                                                (match uu____14778
                                                                 with
                                                                 | (bs3, f_b,
                                                                    g_b) ->
                                                                    let g_sort
                                                                    =
                                                                    let uu____15183
                                                                    =
                                                                    let uu____15184
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    (FStar_Pervasives_Native.fst
                                                                    g_b).FStar_Syntax_Syntax.sort in
                                                                    uu____15184.FStar_Syntax_Syntax.n in
                                                                    match uu____15183
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (uu____15189,
                                                                    c2) ->
                                                                    FStar_Syntax_Util.comp_result
                                                                    c2 in
                                                                    validate_layered_effect_binders
                                                                    env1 bs3
                                                                    [
                                                                    (FStar_Pervasives_Native.fst
                                                                    f_b).FStar_Syntax_Syntax.sort;
                                                                    g_sort;
                                                                    res_t] r)));
                                                      (let uu____15214 =
                                                         let uu____15220 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____15220) in
                                                       FStar_Errors.log_issue
                                                         r uu____15214);
                                                      (let uu____15224 =
                                                         let uu____15225 =
                                                           FStar_All.pipe_right
                                                             k1
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1) in
                                                         (us1, uu____15225) in
                                                       ((us1, t),
                                                         uu____15224))))))))))))
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
            let uu____15274 =
              let uu____15276 =
                FStar_All.pipe_right m FStar_Ident.ident_of_lid in
              FStar_All.pipe_right uu____15276 FStar_Ident.string_of_id in
            let uu____15278 =
              let uu____15280 =
                let uu____15282 =
                  FStar_All.pipe_right n FStar_Ident.ident_of_lid in
                FStar_All.pipe_right uu____15282 FStar_Ident.string_of_id in
              Prims.op_Hat " <: " uu____15280 in
            Prims.op_Hat uu____15274 uu____15278 in
          let uu____15285 =
            check_and_gen env0 combinator_name "polymonadic_subcomp"
              Prims.int_one ts in
          match uu____15285 with
          | (us, t, ty) ->
              let uu____15301 = FStar_Syntax_Subst.open_univ_vars us ty in
              (match uu____15301 with
               | (us1, ty1) ->
                   let env = FStar_TypeChecker_Env.push_univ_vars env0 us1 in
                   (check_no_subtyping_for_layered_combinator env ty1
                      FStar_Pervasives_Native.None;
                    (let uu____15314 =
                       let uu____15319 = FStar_Syntax_Util.type_u () in
                       FStar_All.pipe_right uu____15319
                         (fun uu____15336 ->
                            match uu____15336 with
                            | (t1, u) ->
                                let uu____15347 =
                                  let uu____15348 =
                                    FStar_Syntax_Syntax.gen_bv "a"
                                      FStar_Pervasives_Native.None t1 in
                                  FStar_All.pipe_right uu____15348
                                    FStar_Syntax_Syntax.mk_binder in
                                (uu____15347, u)) in
                     match uu____15314 with
                     | (a, u) ->
                         let rest_bs =
                           let uu____15365 =
                             let uu____15366 =
                               FStar_Syntax_Subst.compress ty1 in
                             uu____15366.FStar_Syntax_Syntax.n in
                           match uu____15365 with
                           | FStar_Syntax_Syntax.Tm_arrow (bs, uu____15378)
                               when
                               (FStar_List.length bs) >= (Prims.of_int (2))
                               ->
                               let uu____15406 =
                                 FStar_Syntax_Subst.open_binders bs in
                               (match uu____15406 with
                                | (a', uu____15416)::bs1 ->
                                    let uu____15436 =
                                      let uu____15437 =
                                        FStar_All.pipe_right bs1
                                          (FStar_List.splitAt
                                             ((FStar_List.length bs1) -
                                                Prims.int_one)) in
                                      FStar_All.pipe_right uu____15437
                                        FStar_Pervasives_Native.fst in
                                    let uu____15535 =
                                      let uu____15548 =
                                        let uu____15551 =
                                          let uu____15552 =
                                            let uu____15559 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                (FStar_Pervasives_Native.fst
                                                   a) in
                                            (a', uu____15559) in
                                          FStar_Syntax_Syntax.NT uu____15552 in
                                        [uu____15551] in
                                      FStar_Syntax_Subst.subst_binders
                                        uu____15548 in
                                    FStar_All.pipe_right uu____15436
                                      uu____15535)
                           | uu____15574 ->
                               let uu____15575 =
                                 let uu____15581 =
                                   let uu____15583 =
                                     FStar_Syntax_Print.tag_of_term t in
                                   let uu____15585 =
                                     FStar_Syntax_Print.term_to_string t in
                                   FStar_Util.format3
                                     "Type of polymonadic subcomp %s is not an arrow with >= 2 binders (%s::%s)"
                                     combinator_name uu____15583 uu____15585 in
                                 (FStar_Errors.Fatal_UnexpectedEffect,
                                   uu____15581) in
                               FStar_Errors.raise_error uu____15575 r in
                         let bs = a :: rest_bs in
                         let uu____15612 =
                           let uu____15623 =
                             let uu____15628 =
                               FStar_TypeChecker_Env.push_binders env bs in
                             let uu____15629 =
                               let uu____15630 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst in
                               FStar_All.pipe_right uu____15630
                                 FStar_Syntax_Syntax.bv_to_name in
                             FStar_TypeChecker_Util.fresh_effect_repr_en
                               uu____15628 r m u uu____15629 in
                           match uu____15623 with
                           | (repr, g) ->
                               let uu____15651 =
                                 let uu____15658 =
                                   FStar_Syntax_Syntax.gen_bv "f"
                                     FStar_Pervasives_Native.None repr in
                                 FStar_All.pipe_right uu____15658
                                   FStar_Syntax_Syntax.mk_binder in
                               (uu____15651, g) in
                         (match uu____15612 with
                          | (f, guard_f) ->
                              let uu____15690 =
                                let uu____15695 =
                                  FStar_TypeChecker_Env.push_binders env bs in
                                let uu____15696 =
                                  let uu____15697 =
                                    FStar_All.pipe_right a
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____15697
                                    FStar_Syntax_Syntax.bv_to_name in
                                FStar_TypeChecker_Util.fresh_effect_repr_en
                                  uu____15695 r n u uu____15696 in
                              (match uu____15690 with
                               | (ret_t, guard_ret_t) ->
                                   let uu____15712 =
                                     let uu____15717 =
                                       FStar_TypeChecker_Env.push_binders env
                                         bs in
                                     let uu____15718 =
                                       FStar_Util.format1
                                         "implicit for pure_wp in checking polymonadic subcomp %s"
                                         combinator_name in
                                     pure_wp_uvar uu____15717 ret_t
                                       uu____15718 r in
                                   (match uu____15712 with
                                    | (pure_wp_uvar1, guard_wp) ->
                                        let c =
                                          let uu____15728 =
                                            let uu____15729 =
                                              let uu____15730 =
                                                FStar_TypeChecker_Env.new_u_univ
                                                  () in
                                              [uu____15730] in
                                            let uu____15731 =
                                              let uu____15742 =
                                                FStar_All.pipe_right
                                                  pure_wp_uvar1
                                                  FStar_Syntax_Syntax.as_arg in
                                              [uu____15742] in
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = uu____15729;
                                              FStar_Syntax_Syntax.effect_name
                                                =
                                                FStar_Parser_Const.effect_PURE_lid;
                                              FStar_Syntax_Syntax.result_typ
                                                = ret_t;
                                              FStar_Syntax_Syntax.effect_args
                                                = uu____15731;
                                              FStar_Syntax_Syntax.flags = []
                                            } in
                                          FStar_Syntax_Syntax.mk_Comp
                                            uu____15728 in
                                        let k =
                                          FStar_Syntax_Util.arrow
                                            (FStar_List.append bs [f]) c in
                                        ((let uu____15797 =
                                            FStar_All.pipe_left
                                              (FStar_TypeChecker_Env.debug
                                                 env)
                                              (FStar_Options.Other
                                                 "LayeredEffectsTc") in
                                          if uu____15797
                                          then
                                            let uu____15802 =
                                              FStar_Syntax_Print.term_to_string
                                                k in
                                            FStar_Util.print2
                                              "Expected type of polymonadic subcomp %s before unification: %s\n"
                                              combinator_name uu____15802
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
                                             let uu____15812 =
                                               FStar_All.pipe_right k
                                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                    env) in
                                             FStar_All.pipe_right uu____15812
                                               (FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.Beta;
                                                  FStar_TypeChecker_Env.Eager_unfolding]
                                                  env) in
                                           (let uu____15816 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env)
                                                (FStar_Options.Other
                                                   "LayeredEffectsTc") in
                                            if uu____15816
                                            then
                                              let uu____15821 =
                                                FStar_Syntax_Print.tscheme_to_string
                                                  (us1, k1) in
                                              FStar_Util.print2
                                                "Polymonadic subcomp %s type after unification : %s\n"
                                                combinator_name uu____15821
                                            else ());
                                           (let uu____15831 =
                                              let uu____15832 =
                                                FStar_Syntax_Subst.compress
                                                  k1 in
                                              uu____15832.FStar_Syntax_Syntax.n in
                                            match uu____15831 with
                                            | FStar_Syntax_Syntax.Tm_arrow
                                                (bs1, c1) ->
                                                let uu____15857 =
                                                  FStar_Syntax_Subst.open_comp
                                                    bs1 c1 in
                                                (match uu____15857 with
                                                 | (bs2, c2) ->
                                                     let res_t =
                                                       FStar_Syntax_Util.comp_result
                                                         c2 in
                                                     let uu____15867 =
                                                       let uu____15886 =
                                                         FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs2)
                                                              - Prims.int_one)
                                                           bs2 in
                                                       FStar_All.pipe_right
                                                         uu____15886
                                                         (fun uu____15963 ->
                                                            match uu____15963
                                                            with
                                                            | (l1, l2) ->
                                                                let uu____16036
                                                                  =
                                                                  FStar_List.tl
                                                                    l1 in
                                                                let uu____16051
                                                                  =
                                                                  FStar_List.hd
                                                                    l2 in
                                                                (uu____16036,
                                                                  uu____16051)) in
                                                     (match uu____15867 with
                                                      | (bs3, f_b) ->
                                                          validate_layered_effect_binders
                                                            env bs3
                                                            [(FStar_Pervasives_Native.fst
                                                                f_b).FStar_Syntax_Syntax.sort;
                                                            res_t] r)));
                                           (let uu____16111 =
                                              let uu____16117 =
                                                FStar_Util.format1
                                                  "Polymonadic subcomp (%s in this case) is an experimental feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                  combinator_name in
                                              (FStar_Errors.Warning_BleedingEdge_Feature,
                                                uu____16117) in
                                            FStar_Errors.log_issue r
                                              uu____16111);
                                           (let uu____16121 =
                                              let uu____16122 =
                                                FStar_All.pipe_right k1
                                                  (FStar_Syntax_Subst.close_univ_vars
                                                     us1) in
                                              (us1, uu____16122) in
                                            ((us1, t), uu____16121)))))))))))