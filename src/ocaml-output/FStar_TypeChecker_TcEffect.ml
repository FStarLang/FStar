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
        fun n1  ->
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
                               (if (FStar_List.length g_us) <> n1
                                then
                                  (let error =
                                     let uu____145 =
                                       FStar_Util.string_of_int n1  in
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
        (match k with
         | FStar_Pervasives_Native.None  ->
             let uu____348 =
               FStar_TypeChecker_TcTerm.tc_trivial_guard
                 (let uu___55_355 = env  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___55_355.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___55_355.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___55_355.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___55_355.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___55_355.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___55_355.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___55_355.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___55_355.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___55_355.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___55_355.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___55_355.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___55_355.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___55_355.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___55_355.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___55_355.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___55_355.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___55_355.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict = true;
                    FStar_TypeChecker_Env.is_iface =
                      (uu___55_355.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___55_355.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___55_355.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___55_355.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___55_355.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___55_355.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___55_355.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___55_355.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___55_355.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___55_355.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___55_355.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___55_355.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___55_355.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___55_355.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___55_355.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___55_355.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___55_355.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___55_355.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___55_355.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___55_355.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___55_355.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___55_355.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___55_355.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___55_355.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___55_355.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___55_355.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___55_355.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___55_355.FStar_TypeChecker_Env.erasable_types_tab)
                  }) t
                in
             ()
         | FStar_Pervasives_Native.Some k1 ->
             let uu____358 =
               FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                 (let uu___59_361 = env  in
                  {
                    FStar_TypeChecker_Env.solver =
                      (uu___59_361.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (uu___59_361.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (uu___59_361.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (uu___59_361.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (uu___59_361.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (uu___59_361.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (uu___59_361.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (uu___59_361.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (uu___59_361.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (uu___59_361.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (uu___59_361.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (uu___59_361.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (uu___59_361.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (uu___59_361.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (uu___59_361.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (uu___59_361.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq =
                      (uu___59_361.FStar_TypeChecker_Env.use_eq);
                    FStar_TypeChecker_Env.use_eq_strict = true;
                    FStar_TypeChecker_Env.is_iface =
                      (uu___59_361.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (uu___59_361.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (uu___59_361.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (uu___59_361.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (uu___59_361.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (uu___59_361.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (uu___59_361.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (uu___59_361.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.tc_term =
                      (uu___59_361.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.type_of =
                      (uu___59_361.FStar_TypeChecker_Env.type_of);
                    FStar_TypeChecker_Env.universe_of =
                      (uu___59_361.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.check_type_of =
                      (uu___59_361.FStar_TypeChecker_Env.check_type_of);
                    FStar_TypeChecker_Env.use_bv_sorts =
                      (uu___59_361.FStar_TypeChecker_Env.use_bv_sorts);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (uu___59_361.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (uu___59_361.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (uu___59_361.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (uu___59_361.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (uu___59_361.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.splice =
                      (uu___59_361.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (uu___59_361.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (uu___59_361.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.is_native_tactic =
                      (uu___59_361.FStar_TypeChecker_Env.is_native_tactic);
                    FStar_TypeChecker_Env.identifier_info =
                      (uu___59_361.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (uu___59_361.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (uu___59_361.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (uu___59_361.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (uu___59_361.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (uu___59_361.FStar_TypeChecker_Env.erasable_types_tab)
                  }) t k1
                in
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
        (let uu____384 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "LayeredEffects")
            in
         if uu____384
         then
           let uu____389 = FStar_Syntax_Print.eff_decl_to_string false ed  in
           FStar_Util.print1 "Typechecking layered effect: \n\t%s\n"
             uu____389
         else ());
        if
          ((FStar_List.length ed.FStar_Syntax_Syntax.univs) <> Prims.int_zero)
            ||
            ((FStar_List.length ed.FStar_Syntax_Syntax.binders) <>
               Prims.int_zero)
        then
          (let uu____407 =
             FStar_Ident.range_of_lid ed.FStar_Syntax_Syntax.mname  in
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_UnexpectedEffect,
               (Prims.op_Hat
                  "Binders are not supported for layered effects ("
                  (Prims.op_Hat
                     (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str ")")))
             uu____407)
        else ();
        (let log_combinator s uu____436 =
           match uu____436 with
           | (us,t,ty) ->
               let uu____465 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                   (FStar_Options.Other "LayeredEffects")
                  in
               if uu____465
               then
                 let uu____470 = FStar_Syntax_Print.tscheme_to_string (us, t)
                    in
                 let uu____476 =
                   FStar_Syntax_Print.tscheme_to_string (us, ty)  in
                 FStar_Util.print4 "Typechecked %s:%s = %s:%s\n"
                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str s uu____470
                   uu____476
               else ()
            in
         let fresh_a_and_u_a a =
           let uu____501 = FStar_Syntax_Util.type_u ()  in
           FStar_All.pipe_right uu____501
             (fun uu____518  ->
                match uu____518 with
                | (t,u) ->
                    let uu____529 =
                      let uu____530 =
                        FStar_Syntax_Syntax.gen_bv a
                          FStar_Pervasives_Native.None t
                         in
                      FStar_All.pipe_right uu____530
                        FStar_Syntax_Syntax.mk_binder
                       in
                    (uu____529, u))
            in
         let fresh_x_a x a =
           let uu____544 =
             let uu____545 =
               let uu____546 =
                 FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
               FStar_All.pipe_right uu____546 FStar_Syntax_Syntax.bv_to_name
                in
             FStar_Syntax_Syntax.gen_bv x FStar_Pervasives_Native.None
               uu____545
              in
           FStar_All.pipe_right uu____544 FStar_Syntax_Syntax.mk_binder  in
         let check_and_gen1 =
           check_and_gen env0 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
            in
         let signature =
           let r =
             (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
              in
           let uu____598 =
             check_and_gen1 "signature" Prims.int_one
               ed.FStar_Syntax_Syntax.signature
              in
           match uu____598 with
           | (sig_us,sig_t,sig_ty) ->
               let uu____622 = FStar_Syntax_Subst.open_univ_vars sig_us sig_t
                  in
               (match uu____622 with
                | (us,t) ->
                    let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                       in
                    let uu____642 = fresh_a_and_u_a "a"  in
                    (match uu____642 with
                     | (a,u) ->
                         let rest_bs =
                           let uu____663 =
                             let uu____664 =
                               FStar_All.pipe_right a
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_All.pipe_right uu____664
                               FStar_Syntax_Syntax.bv_to_name
                              in
                           FStar_TypeChecker_Util.layered_effect_indices_as_binders
                             env r ed.FStar_Syntax_Syntax.mname
                             (sig_us, sig_t) u uu____663
                            in
                         let bs = a :: rest_bs  in
                         let k =
                           let uu____695 =
                             FStar_Syntax_Syntax.mk_Total
                               FStar_Syntax_Syntax.teff
                              in
                           FStar_Syntax_Util.arrow bs uu____695  in
                         let g_eq = FStar_TypeChecker_Rel.teq env t k  in
                         (FStar_TypeChecker_Rel.force_trivial_guard env g_eq;
                          (let uu____700 =
                             let uu____703 =
                               FStar_All.pipe_right k
                                 (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                    env)
                                in
                             FStar_Syntax_Subst.close_univ_vars us uu____703
                              in
                           (sig_us, uu____700, sig_ty)))))
            in
         log_combinator "signature" signature;
         (let uu____712 =
            let repr_ts =
              let uu____734 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_eff_repr  in
              FStar_All.pipe_right uu____734 FStar_Util.must  in
            let r =
              (FStar_Pervasives_Native.snd repr_ts).FStar_Syntax_Syntax.pos
               in
            let uu____762 = check_and_gen1 "repr" Prims.int_one repr_ts  in
            match uu____762 with
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
                  let uu____793 =
                    let uu____794 = FStar_Syntax_Subst.compress repr_t1  in
                    uu____794.FStar_Syntax_Syntax.n  in
                  match uu____793 with
                  | FStar_Syntax_Syntax.Tm_abs (uu____797,t,uu____799) ->
                      let uu____824 =
                        let uu____825 = FStar_Syntax_Subst.compress t  in
                        uu____825.FStar_Syntax_Syntax.n  in
                      (match uu____824 with
                       | FStar_Syntax_Syntax.Tm_arrow (uu____828,c) ->
                           let uu____850 =
                             FStar_All.pipe_right c
                               FStar_Syntax_Util.comp_effect_name
                              in
                           FStar_All.pipe_right uu____850
                             (FStar_TypeChecker_Env.norm_eff_name env0)
                       | uu____853 ->
                           let uu____854 =
                             let uu____860 =
                               let uu____862 =
                                 FStar_All.pipe_right
                                   ed.FStar_Syntax_Syntax.mname
                                   FStar_Ident.string_of_lid
                                  in
                               let uu____865 =
                                 FStar_Syntax_Print.term_to_string t  in
                               FStar_Util.format2
                                 "repr body for %s is not an arrow (%s)"
                                 uu____862 uu____865
                                in
                             (FStar_Errors.Fatal_UnexpectedEffect, uu____860)
                              in
                           FStar_Errors.raise_error uu____854 r)
                  | uu____869 ->
                      let uu____870 =
                        let uu____876 =
                          let uu____878 =
                            FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                              FStar_Ident.string_of_lid
                             in
                          let uu____881 =
                            FStar_Syntax_Print.term_to_string repr_t1  in
                          FStar_Util.format2
                            "repr for %s is not an abstraction (%s)"
                            uu____878 uu____881
                           in
                        (FStar_Errors.Fatal_UnexpectedEffect, uu____876)  in
                      FStar_Errors.raise_error uu____870 r
                   in
                ((let uu____886 =
                    (FStar_All.pipe_right quals
                       (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))
                      &&
                      (let uu____892 =
                         FStar_TypeChecker_Env.is_total_effect env0
                           underlying_effect_lid
                          in
                       Prims.op_Negation uu____892)
                     in
                  if uu____886
                  then
                    let uu____895 =
                      let uu____901 =
                        let uu____903 =
                          FStar_All.pipe_right ed.FStar_Syntax_Syntax.mname
                            FStar_Ident.string_of_lid
                           in
                        let uu____906 =
                          FStar_All.pipe_right underlying_effect_lid
                            FStar_Ident.string_of_lid
                           in
                        FStar_Util.format2
                          "Effect %s is marked total but its underlying effect %s is not total"
                          uu____903 uu____906
                         in
                      (FStar_Errors.Fatal_DivergentComputationCannotBeIncludedInTotal,
                        uu____901)
                       in
                    FStar_Errors.raise_error uu____895 r
                  else ());
                 (let uu____913 =
                    FStar_Syntax_Subst.open_univ_vars repr_us repr_ty  in
                  match uu____913 with
                  | (us,ty) ->
                      let env = FStar_TypeChecker_Env.push_univ_vars env0 us
                         in
                      let uu____937 = fresh_a_and_u_a "a"  in
                      (match uu____937 with
                       | (a,u) ->
                           let rest_bs =
                             let signature_ts =
                               let uu____963 = signature  in
                               match uu____963 with
                               | (us1,t,uu____978) -> (us1, t)  in
                             let uu____995 =
                               let uu____996 =
                                 FStar_All.pipe_right a
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____996
                                 FStar_Syntax_Syntax.bv_to_name
                                in
                             FStar_TypeChecker_Util.layered_effect_indices_as_binders
                               env r ed.FStar_Syntax_Syntax.mname
                               signature_ts u uu____995
                              in
                           let bs = a :: rest_bs  in
                           let k =
                             let uu____1023 =
                               let uu____1026 = FStar_Syntax_Util.type_u ()
                                  in
                               FStar_All.pipe_right uu____1026
                                 (fun uu____1039  ->
                                    match uu____1039 with
                                    | (t,u1) ->
                                        let uu____1046 =
                                          let uu____1049 =
                                            FStar_TypeChecker_Env.new_u_univ
                                              ()
                                             in
                                          FStar_Pervasives_Native.Some
                                            uu____1049
                                           in
                                        FStar_Syntax_Syntax.mk_Total' t
                                          uu____1046)
                                in
                             FStar_Syntax_Util.arrow bs uu____1023  in
                           let g = FStar_TypeChecker_Rel.teq env ty k  in
                           (FStar_TypeChecker_Rel.force_trivial_guard env g;
                            (let uu____1052 =
                               let uu____1065 =
                                 let uu____1068 =
                                   FStar_All.pipe_right k
                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                        env)
                                    in
                                 FStar_Syntax_Subst.close_univ_vars us
                                   uu____1068
                                  in
                               (repr_us, repr_t, uu____1065)  in
                             (uu____1052, underlying_effect_lid))))))
             in
          match uu____712 with
          | (repr,underlying_effect_lid) ->
              (log_combinator "repr" repr;
               (let fresh_repr r env u a_tm =
                  let signature_ts =
                    let uu____1141 = signature  in
                    match uu____1141 with | (us,t,uu____1156) -> (us, t)  in
                  let repr_ts =
                    let uu____1174 = repr  in
                    match uu____1174 with | (us,t,uu____1189) -> (us, t)  in
                  FStar_TypeChecker_Util.fresh_effect_repr env r
                    ed.FStar_Syntax_Syntax.mname signature_ts
                    (FStar_Pervasives_Native.Some repr_ts) u a_tm
                   in
                let not_an_arrow_error comb n1 t r =
                  let uu____1239 =
                    let uu____1245 =
                      let uu____1247 = FStar_Util.string_of_int n1  in
                      let uu____1249 = FStar_Syntax_Print.tag_of_term t  in
                      let uu____1251 = FStar_Syntax_Print.term_to_string t
                         in
                      FStar_Util.format5
                        "Type of %s:%s is not an arrow with >= %s binders (%s::%s)"
                        (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str comb
                        uu____1247 uu____1249 uu____1251
                       in
                    (FStar_Errors.Fatal_UnexpectedEffect, uu____1245)  in
                  FStar_Errors.raise_error uu____1239 r  in
                let return_repr =
                  let return_repr_ts =
                    let uu____1281 =
                      FStar_All.pipe_right ed
                        FStar_Syntax_Util.get_return_repr
                       in
                    FStar_All.pipe_right uu____1281 FStar_Util.must  in
                  let r =
                    (FStar_Pervasives_Native.snd return_repr_ts).FStar_Syntax_Syntax.pos
                     in
                  let uu____1309 =
                    check_and_gen1 "return_repr" Prims.int_one return_repr_ts
                     in
                  match uu____1309 with
                  | (ret_us,ret_t,ret_ty) ->
                      let uu____1333 =
                        FStar_Syntax_Subst.open_univ_vars ret_us ret_ty  in
                      (match uu____1333 with
                       | (us,ty) ->
                           let env =
                             FStar_TypeChecker_Env.push_univ_vars env0 us  in
                           (check_no_subtyping_for_layered_combinator env ty
                              FStar_Pervasives_Native.None;
                            (let uu____1354 = fresh_a_and_u_a "a"  in
                             match uu____1354 with
                             | (a,u_a) ->
                                 let x_a = fresh_x_a "x" a  in
                                 let rest_bs =
                                   let uu____1385 =
                                     let uu____1386 =
                                       FStar_Syntax_Subst.compress ty  in
                                     uu____1386.FStar_Syntax_Syntax.n  in
                                   match uu____1385 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____1398) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (2))
                                       ->
                                       let uu____1426 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____1426 with
                                        | (a',uu____1436)::(x',uu____1438)::bs1
                                            ->
                                            let uu____1468 =
                                              let uu____1469 =
                                                let uu____1474 =
                                                  let uu____1477 =
                                                    let uu____1478 =
                                                      let uu____1485 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____1485)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____1478
                                                     in
                                                  [uu____1477]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____1474
                                                 in
                                              FStar_All.pipe_right bs1
                                                uu____1469
                                               in
                                            let uu____1492 =
                                              let uu____1505 =
                                                let uu____1508 =
                                                  let uu____1509 =
                                                    let uu____1516 =
                                                      FStar_Syntax_Syntax.bv_to_name
                                                        (FStar_Pervasives_Native.fst
                                                           x_a)
                                                       in
                                                    (x', uu____1516)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____1509
                                                   in
                                                [uu____1508]  in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____1505
                                               in
                                            FStar_All.pipe_right uu____1468
                                              uu____1492)
                                   | uu____1531 ->
                                       not_an_arrow_error "return"
                                         (Prims.of_int (2)) ty r
                                    in
                                 let bs = a :: x_a :: rest_bs  in
                                 let uu____1555 =
                                   let uu____1560 =
                                     FStar_TypeChecker_Env.push_binders env
                                       bs
                                      in
                                   let uu____1561 =
                                     FStar_All.pipe_right
                                       (FStar_Pervasives_Native.fst a)
                                       FStar_Syntax_Syntax.bv_to_name
                                      in
                                   fresh_repr r uu____1560 u_a uu____1561  in
                                 (match uu____1555 with
                                  | (repr1,g) ->
                                      let k =
                                        let uu____1581 =
                                          FStar_Syntax_Syntax.mk_Total' repr1
                                            (FStar_Pervasives_Native.Some u_a)
                                           in
                                        FStar_Syntax_Util.arrow bs uu____1581
                                         in
                                      let g_eq =
                                        FStar_TypeChecker_Rel.teq env ty k
                                         in
                                      ((let uu____1586 =
                                          FStar_TypeChecker_Env.conj_guard g
                                            g_eq
                                           in
                                        FStar_TypeChecker_Rel.force_trivial_guard
                                          env uu____1586);
                                       (let uu____1587 =
                                          let uu____1590 =
                                            FStar_All.pipe_right k
                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                 env)
                                             in
                                          FStar_All.pipe_right uu____1590
                                            (FStar_Syntax_Subst.close_univ_vars
                                               us)
                                           in
                                        (ret_us, ret_t, uu____1587)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1619 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1619 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1631 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1631 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1655 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1655 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1676 = fresh_a_and_u_a "a"  in
                              match uu____1676 with
                              | (a,u_a) ->
                                  let uu____1696 = fresh_a_and_u_a "b"  in
                                  (match uu____1696 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1725 =
                                           let uu____1726 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1726.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1725 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1738) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1766 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1766 with
                                              | (a',uu____1776)::(b',uu____1778)::bs1
                                                  ->
                                                  let uu____1808 =
                                                    let uu____1809 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1809
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1907 =
                                                    let uu____1920 =
                                                      let uu____1923 =
                                                        let uu____1924 =
                                                          let uu____1931 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1931)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1924
                                                         in
                                                      let uu____1938 =
                                                        let uu____1941 =
                                                          let uu____1942 =
                                                            let uu____1949 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1949)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1942
                                                           in
                                                        [uu____1941]  in
                                                      uu____1923 ::
                                                        uu____1938
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1920
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1808 uu____1907)
                                         | uu____1964 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1988 =
                                         let uu____1999 =
                                           let uu____2004 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2005 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2004 u_a
                                             uu____2005
                                            in
                                         match uu____1999 with
                                         | (repr1,g) ->
                                             let uu____2020 =
                                               let uu____2027 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2027
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2020, g)
                                          in
                                       (match uu____1988 with
                                        | (f,guard_f) ->
                                            let uu____2067 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2080 =
                                                let uu____2085 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2104 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2085 u_b
                                                  uu____2104
                                                 in
                                              match uu____2080 with
                                              | (repr1,g) ->
                                                  let uu____2119 =
                                                    let uu____2126 =
                                                      let uu____2127 =
                                                        let uu____2128 =
                                                          let uu____2131 =
                                                            let uu____2134 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2134
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2131
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2128
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2127
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2126
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2119, g)
                                               in
                                            (match uu____2067 with
                                             | (g,guard_g) ->
                                                 let uu____2186 =
                                                   let uu____2191 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2192 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2191
                                                     u_b uu____2192
                                                    in
                                                 (match uu____2186 with
                                                  | (repr1,guard_repr) ->
                                                      let uu____2209 =
                                                        let uu____2214 =
                                                          FStar_TypeChecker_Env.push_binders
                                                            env bs
                                                           in
                                                        let uu____2215 =
                                                          FStar_Util.format1
                                                            "implicit for pure_wp in checking bind for %s"
                                                            (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                           in
                                                        pure_wp_uvar
                                                          uu____2214 repr1
                                                          uu____2215 r
                                                         in
                                                      (match uu____2209 with
                                                       | (pure_wp_uvar1,g_pure_wp_uvar)
                                                           ->
                                                           let k =
                                                             let uu____2235 =
                                                               let uu____2238
                                                                 =
                                                                 let uu____2239
                                                                   =
                                                                   let uu____2240
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                   [uu____2240]
                                                                    in
                                                                 let uu____2241
                                                                   =
                                                                   let uu____2252
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    pure_wp_uvar1
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                   [uu____2252]
                                                                    in
                                                                 {
                                                                   FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____2239;
                                                                   FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    FStar_Parser_Const.effect_PURE_lid;
                                                                   FStar_Syntax_Syntax.result_typ
                                                                    = repr1;
                                                                   FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____2241;
                                                                   FStar_Syntax_Syntax.flags
                                                                    = []
                                                                 }  in
                                                               FStar_Syntax_Syntax.mk_Comp
                                                                 uu____2238
                                                                in
                                                             FStar_Syntax_Util.arrow
                                                               (FStar_List.append
                                                                  bs 
                                                                  [f; g])
                                                               uu____2235
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
                                                            (let uu____2311 =
                                                               let uu____2314
                                                                 =
                                                                 FStar_All.pipe_right
                                                                   k
                                                                   (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                    env)
                                                                  in
                                                               FStar_All.pipe_right
                                                                 uu____2314
                                                                 (FStar_Syntax_Subst.close_univ_vars
                                                                    bind_us)
                                                                in
                                                             (bind_us,
                                                               bind_t,
                                                               uu____2311)))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2343 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2343 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2371 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2371 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2396 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2396
                          then
                            let uu____2401 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2407 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2401 uu____2407
                          else ());
                         (let uu____2416 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2416 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2437 = fresh_a_and_u_a "a"  in
                                match uu____2437 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2466 =
                                        let uu____2467 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2467.FStar_Syntax_Syntax.n  in
                                      match uu____2466 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2479) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2507 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2507 with
                                           | (a',uu____2517)::bs1 ->
                                               let uu____2537 =
                                                 let uu____2538 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2538
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2604 =
                                                 let uu____2617 =
                                                   let uu____2620 =
                                                     let uu____2621 =
                                                       let uu____2628 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2628)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2621
                                                      in
                                                   [uu____2620]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2617
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2537 uu____2604)
                                      | uu____2643 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2661 =
                                      let uu____2672 =
                                        let uu____2677 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2678 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2677 u uu____2678
                                         in
                                      match uu____2672 with
                                      | (repr1,g) ->
                                          let uu____2693 =
                                            let uu____2700 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2700
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2693, g)
                                       in
                                    (match uu____2661 with
                                     | (f,guard_f) ->
                                         let uu____2740 =
                                           let uu____2745 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2746 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2745 u
                                             uu____2746
                                            in
                                         (match uu____2740 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2763 =
                                                let uu____2768 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2769 =
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   in
                                                pure_wp_uvar uu____2768 ret_t
                                                  uu____2769 r
                                                 in
                                              (match uu____2763 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2787 =
                                                       let uu____2788 =
                                                         let uu____2789 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2789]  in
                                                       let uu____2790 =
                                                         let uu____2801 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2801]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2788;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2790;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2787
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2856 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2856
                                                     then
                                                       let uu____2861 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2861
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
                                                     (let uu____2868 =
                                                        let uu____2871 =
                                                          let uu____2872 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2872
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2871
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2868)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2903 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2903 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2919 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2919 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2943 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2943 with
                          | (us,t) ->
                              let uu____2962 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2962 with
                               | (uu____2979,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____2983 = fresh_a_and_u_a "a"  in
                                     match uu____2983 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____3012 =
                                             let uu____3013 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____3013.FStar_Syntax_Syntax.n
                                              in
                                           match uu____3012 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____3025) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3053 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3053 with
                                                | (a',uu____3063)::bs1 ->
                                                    let uu____3083 =
                                                      let uu____3084 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3084
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3182 =
                                                      let uu____3195 =
                                                        let uu____3198 =
                                                          let uu____3199 =
                                                            let uu____3206 =
                                                              let uu____3209
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3209
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3206)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3199
                                                           in
                                                        [uu____3198]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3195
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3083 uu____3182)
                                           | uu____3230 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3248 =
                                           let uu____3259 =
                                             let uu____3264 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3265 =
                                               let uu____3266 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3266
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3264 u_a
                                               uu____3265
                                              in
                                           match uu____3259 with
                                           | (repr1,g) ->
                                               let uu____3287 =
                                                 let uu____3294 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3294
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3287, g)
                                            in
                                         (match uu____3248 with
                                          | (f_bs,guard_f) ->
                                              let uu____3334 =
                                                let uu____3345 =
                                                  let uu____3350 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3351 =
                                                    let uu____3352 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3352
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3350 u_a
                                                    uu____3351
                                                   in
                                                match uu____3345 with
                                                | (repr1,g) ->
                                                    let uu____3373 =
                                                      let uu____3380 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3380
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3373, g)
                                                 in
                                              (match uu____3334 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3427 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3427
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3435 =
                                                     let uu____3440 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3459 =
                                                       let uu____3460 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3460
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3440
                                                       u_a uu____3459
                                                      in
                                                   (match uu____3435 with
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
                                                         (let uu____3520 =
                                                            let uu____3523 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3523
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3520,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3536 =
                        let uu____3539 =
                          let uu____3548 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3548 FStar_Util.must  in
                        FStar_All.pipe_right uu____3539
                          FStar_Pervasives_Native.snd
                         in
                      uu____3536.FStar_Syntax_Syntax.pos  in
                    let uu____3577 = if_then_else1  in
                    match uu____3577 with
                    | (ite_us,ite_t,uu____3592) ->
                        let uu____3605 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3605 with
                         | (us,ite_t1) ->
                             let uu____3612 =
                               let uu____3623 =
                                 let uu____3624 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3624.FStar_Syntax_Syntax.n  in
                               match uu____3623 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3638,uu____3639) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3665 =
                                     let uu____3672 =
                                       let uu____3675 =
                                         let uu____3678 =
                                           let uu____3687 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3687
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3678
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3675
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3672
                                       (fun l  ->
                                          let uu____3831 = l  in
                                          match uu____3831 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3665 with
                                    | (f,g,p) ->
                                        let uu____3856 =
                                          let uu____3857 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3857 bs1
                                           in
                                        let uu____3858 =
                                          let uu____3859 =
                                            let uu____3864 =
                                              let uu____3865 =
                                                let uu____3868 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3868
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3865
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3864
                                             in
                                          uu____3859
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3856, uu____3858, f, g, p))
                               | uu____3895 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3612 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3912 =
                                    let uu____3921 = stronger_repr  in
                                    match uu____3921 with
                                    | (uu____3942,subcomp_t,subcomp_ty) ->
                                        let uu____3957 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3957 with
                                         | (uu____3970,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3981 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3981 with
                                               | (uu____3994,subcomp_ty1) ->
                                                   let uu____3996 =
                                                     let uu____3997 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3997.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3996 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____4009) ->
                                                        let uu____4030 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4030
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4136 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4154 =
                                                 let uu____4159 =
                                                   let uu____4160 =
                                                     let uu____4163 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4183 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4163 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4160
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4159
                                                  in
                                               uu____4154
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4192 = aux f_t  in
                                             let uu____4195 = aux g_t  in
                                             (uu____4192, uu____4195))
                                     in
                                  (match uu____3912 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4212 =
                                         let aux t =
                                           let uu____4229 =
                                             let uu____4236 =
                                               let uu____4237 =
                                                 let uu____4264 =
                                                   let uu____4281 =
                                                     let uu____4290 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4290
                                                      in
                                                   (uu____4281,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4264,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4237
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4236
                                              in
                                           uu____4229
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4331 = aux subcomp_f  in
                                         let uu____4332 = aux subcomp_g  in
                                         (uu____4331, uu____4332)  in
                                       (match uu____4212 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4336 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4336
                                              then
                                                let uu____4341 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4343 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4341 uu____4343
                                              else ());
                                             (let uu____4348 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4348 with
                                              | (uu____4355,uu____4356,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4359 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4359 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4361 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4361 with
                                                    | (uu____4368,uu____4369,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4375 =
                                                              let uu____4380
                                                                =
                                                                let uu____4381
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4381
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4382
                                                                =
                                                                let uu____4383
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4383]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4380
                                                                uu____4382
                                                               in
                                                            uu____4375
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4416 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4416 g_g
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
                        (let uu____4440 =
                           let uu____4446 =
                             let uu____4448 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4448
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4446)
                            in
                         FStar_Errors.raise_error uu____4440 r)
                      else ();
                      (let uu____4455 =
                         let uu____4460 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4460 with
                         | (usubst,us) ->
                             let uu____4483 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4484 =
                               let uu___447_4485 = act  in
                               let uu____4486 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4487 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___447_4485.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___447_4485.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___447_4485.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4486;
                                 FStar_Syntax_Syntax.action_typ = uu____4487
                               }  in
                             (uu____4483, uu____4484)
                          in
                       match uu____4455 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4491 =
                               let uu____4492 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4492.FStar_Syntax_Syntax.n  in
                             match uu____4491 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4518 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4518
                                 then
                                   let repr_ts =
                                     let uu____4522 = repr  in
                                     match uu____4522 with
                                     | (us,t,uu____4537) -> (us, t)  in
                                   let repr1 =
                                     let uu____4555 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4555
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4567 =
                                       let uu____4572 =
                                         let uu____4573 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4573 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4572
                                        in
                                     uu____4567 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4591 =
                                       let uu____4594 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4594
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4591
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4597 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4598 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4598 with
                            | (act_typ1,uu____4606,g_t) ->
                                let uu____4608 =
                                  let uu____4615 =
                                    let uu___472_4616 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___472_4616.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___472_4616.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___472_4616.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___472_4616.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___472_4616.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___472_4616.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___472_4616.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___472_4616.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___472_4616.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___472_4616.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___472_4616.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___472_4616.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___472_4616.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___472_4616.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___472_4616.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___472_4616.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___472_4616.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___472_4616.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___472_4616.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___472_4616.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___472_4616.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___472_4616.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___472_4616.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___472_4616.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___472_4616.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___472_4616.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___472_4616.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___472_4616.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___472_4616.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___472_4616.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___472_4616.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___472_4616.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___472_4616.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___472_4616.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___472_4616.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___472_4616.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___472_4616.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___472_4616.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___472_4616.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___472_4616.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___472_4616.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___472_4616.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___472_4616.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___472_4616.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___472_4616.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4615
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4608 with
                                 | (act_defn,uu____4619,g_d) ->
                                     ((let uu____4622 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4622
                                       then
                                         let uu____4627 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4629 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4627 uu____4629
                                       else ());
                                      (let uu____4634 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4642 =
                                           let uu____4643 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4643.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4642 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4653) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4676 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4676 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4692 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4692 with
                                                   | (a_tm,uu____4712,g_tm)
                                                       ->
                                                       let uu____4726 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4726 with
                                                        | (repr1,g) ->
                                                            let uu____4739 =
                                                              let uu____4742
                                                                =
                                                                let uu____4745
                                                                  =
                                                                  let uu____4748
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4748
                                                                    (
                                                                    fun _4751
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4751)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4745
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4742
                                                               in
                                                            let uu____4752 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4739,
                                                              uu____4752))))
                                         | uu____4755 ->
                                             let uu____4756 =
                                               let uu____4762 =
                                                 let uu____4764 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4764
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4762)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4756 r
                                          in
                                       match uu____4634 with
                                       | (k,g_k) ->
                                           ((let uu____4781 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4781
                                             then
                                               let uu____4786 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4786
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4794 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4794
                                              then
                                                let uu____4799 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4799
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4812 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4812
                                                   in
                                                let repr_args t =
                                                  let uu____4833 =
                                                    let uu____4834 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4834.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4833 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4886 =
                                                        let uu____4887 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4887.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4886 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4896,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4906 ->
                                                           let uu____4907 =
                                                             let uu____4913 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4913)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4907 r)
                                                  | uu____4922 ->
                                                      let uu____4923 =
                                                        let uu____4929 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4929)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4923 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4939 =
                                                  let uu____4940 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4940.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4939 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4965 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4965 with
                                                     | (bs1,c1) ->
                                                         let uu____4972 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4972
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
                                                              let uu____4983
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4983))
                                                | uu____4986 ->
                                                    let uu____4987 =
                                                      let uu____4993 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4993)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4987 r
                                                 in
                                              (let uu____4997 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4997
                                               then
                                                 let uu____5002 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____5002
                                               else ());
                                              (let act2 =
                                                 let uu____5008 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____5008 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___545_5022 =
                                                         act1  in
                                                       let uu____5023 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___545_5022.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___545_5022.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___545_5022.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____5023
                                                       }
                                                     else
                                                       (let uu____5026 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5033
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5033
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____5026
                                                        then
                                                          let uu___550_5038 =
                                                            act1  in
                                                          let uu____5039 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___550_5038.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___550_5038.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___550_5038.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___550_5038.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5039
                                                          }
                                                        else
                                                          (let uu____5042 =
                                                             let uu____5048 =
                                                               let uu____5050
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5052
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____5050
                                                                 uu____5052
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5048)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5042 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5077 =
                      match uu____5077 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5122 =
                        let uu____5123 = tschemes_of repr  in
                        let uu____5128 = tschemes_of return_repr  in
                        let uu____5133 = tschemes_of bind_repr  in
                        let uu____5138 = tschemes_of stronger_repr  in
                        let uu____5143 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5123;
                          FStar_Syntax_Syntax.l_return = uu____5128;
                          FStar_Syntax_Syntax.l_bind = uu____5133;
                          FStar_Syntax_Syntax.l_subcomp = uu____5138;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5143
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5122  in
                    let uu___559_5148 = ed  in
                    let uu____5149 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___559_5148.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___559_5148.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___559_5148.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___559_5148.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5156 = signature  in
                         match uu____5156 with | (us,t,uu____5171) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5149;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___559_5148.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5209 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5209
         then
           let uu____5214 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5214
         else ());
        (let uu____5220 =
           let uu____5225 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5225 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5249 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5249  in
               let uu____5250 =
                 let uu____5257 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5257 bs  in
               (match uu____5250 with
                | (bs1,uu____5263,uu____5264) ->
                    let uu____5265 =
                      let tmp_t =
                        let uu____5275 =
                          let uu____5278 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5283  ->
                                 FStar_Pervasives_Native.Some _5283)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5278
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5275  in
                      let uu____5284 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5284 with
                      | (us,tmp_t1) ->
                          let uu____5301 =
                            let uu____5302 =
                              let uu____5303 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5303
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5302
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5301)
                       in
                    (match uu____5265 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5340 ->
                              let uu____5343 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5350 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5350 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5343
                              then (us, bs2)
                              else
                                (let uu____5361 =
                                   let uu____5367 =
                                     let uu____5369 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5371 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5369 uu____5371
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5367)
                                    in
                                 let uu____5375 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5361
                                   uu____5375))))
            in
         match uu____5220 with
         | (us,bs) ->
             let ed1 =
               let uu___593_5383 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___593_5383.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___593_5383.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___593_5383.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___593_5383.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___593_5383.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___593_5383.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5384 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5384 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5403 =
                    let uu____5408 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5408  in
                  (match uu____5403 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5429 =
                           match uu____5429 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5449 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5449 t  in
                               let uu____5458 =
                                 let uu____5459 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5459 t1  in
                               (us1, uu____5458)
                            in
                         let uu___607_5464 = ed1  in
                         let uu____5465 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5466 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5467 =
                           FStar_List.map
                             (fun a  ->
                                let uu___610_5475 = a  in
                                let uu____5476 =
                                  let uu____5477 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5477  in
                                let uu____5488 =
                                  let uu____5489 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5489  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___610_5475.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___610_5475.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___610_5475.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___610_5475.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5476;
                                  FStar_Syntax_Syntax.action_typ = uu____5488
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___607_5464.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___607_5464.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___607_5464.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___607_5464.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5465;
                           FStar_Syntax_Syntax.combinators = uu____5466;
                           FStar_Syntax_Syntax.actions = uu____5467;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___607_5464.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5501 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5501
                         then
                           let uu____5506 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5506
                         else ());
                        (let env =
                           let uu____5513 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5513
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5548 k =
                           match uu____5548 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5568 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5568 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5577 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5577 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5578 =
                                            let uu____5585 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5585 t1
                                             in
                                          (match uu____5578 with
                                           | (t2,uu____5587,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5590 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5590 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5606 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5608 =
                                                 let uu____5610 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5610
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5606 uu____5608
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5625 ->
                                               let uu____5626 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5633 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5633 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5626
                                               then (g_us, t3)
                                               else
                                                 (let uu____5644 =
                                                    let uu____5650 =
                                                      let uu____5652 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5654 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5652
                                                        uu____5654
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5650)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5644
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5662 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5662
                          then
                            let uu____5667 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5667
                          else ());
                         (let fresh_a_and_wp uu____5683 =
                            let fail1 t =
                              let uu____5696 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5696
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5712 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5712 with
                            | (uu____5723,signature1) ->
                                let uu____5725 =
                                  let uu____5726 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5726.FStar_Syntax_Syntax.n  in
                                (match uu____5725 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5736) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5765)::(wp,uu____5767)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5796 -> fail1 signature1)
                                 | uu____5797 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5811 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5811
                            then
                              let uu____5816 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5816
                            else ()  in
                          let ret_wp =
                            let uu____5822 = fresh_a_and_wp ()  in
                            match uu____5822 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5838 =
                                    let uu____5847 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5854 =
                                      let uu____5863 =
                                        let uu____5870 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5870
                                         in
                                      [uu____5863]  in
                                    uu____5847 :: uu____5854  in
                                  let uu____5889 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5838
                                    uu____5889
                                   in
                                let uu____5892 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5892
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5906 = fresh_a_and_wp ()  in
                             match uu____5906 with
                             | (a,wp_sort_a) ->
                                 let uu____5919 = fresh_a_and_wp ()  in
                                 (match uu____5919 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5935 =
                                          let uu____5944 =
                                            let uu____5951 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5951
                                             in
                                          [uu____5944]  in
                                        let uu____5964 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5935
                                          uu____5964
                                         in
                                      let k =
                                        let uu____5970 =
                                          let uu____5979 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5986 =
                                            let uu____5995 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____6002 =
                                              let uu____6011 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____6018 =
                                                let uu____6027 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6034 =
                                                  let uu____6043 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6043]  in
                                                uu____6027 :: uu____6034  in
                                              uu____6011 :: uu____6018  in
                                            uu____5995 :: uu____6002  in
                                          uu____5979 :: uu____5986  in
                                        let uu____6086 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5970
                                          uu____6086
                                         in
                                      let uu____6089 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6089
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6103 = fresh_a_and_wp ()  in
                              match uu____6103 with
                              | (a,wp_sort_a) ->
                                  let uu____6116 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6116 with
                                   | (t,uu____6122) ->
                                       let k =
                                         let uu____6126 =
                                           let uu____6135 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6142 =
                                             let uu____6151 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6158 =
                                               let uu____6167 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6167]  in
                                             uu____6151 :: uu____6158  in
                                           uu____6135 :: uu____6142  in
                                         let uu____6198 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6126
                                           uu____6198
                                          in
                                       let uu____6201 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6201
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6215 = fresh_a_and_wp ()  in
                               match uu____6215 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6229 =
                                       let uu____6232 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6232
                                        in
                                     let uu____6233 =
                                       let uu____6234 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6234
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6229
                                       uu____6233
                                      in
                                   let k =
                                     let uu____6246 =
                                       let uu____6255 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6262 =
                                         let uu____6271 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6278 =
                                           let uu____6287 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6294 =
                                             let uu____6303 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6303]  in
                                           uu____6287 :: uu____6294  in
                                         uu____6271 :: uu____6278  in
                                       uu____6255 :: uu____6262  in
                                     let uu____6340 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6246
                                       uu____6340
                                      in
                                   let uu____6343 =
                                     let uu____6348 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6348
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6343
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6380 = fresh_a_and_wp ()  in
                                match uu____6380 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6396 =
                                        let uu____6405 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6412 =
                                          let uu____6421 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6421]  in
                                        uu____6405 :: uu____6412  in
                                      let uu____6446 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6396
                                        uu____6446
                                       in
                                    let uu____6449 =
                                      let uu____6454 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6454
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6449
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6470 = fresh_a_and_wp ()  in
                                 match uu____6470 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6484 =
                                         let uu____6487 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6487
                                          in
                                       let uu____6488 =
                                         let uu____6489 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6489
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6484
                                         uu____6488
                                        in
                                     let wp_sort_b_a =
                                       let uu____6501 =
                                         let uu____6510 =
                                           let uu____6517 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6517
                                            in
                                         [uu____6510]  in
                                       let uu____6530 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6501
                                         uu____6530
                                        in
                                     let k =
                                       let uu____6536 =
                                         let uu____6545 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6552 =
                                           let uu____6561 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6568 =
                                             let uu____6577 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6577]  in
                                           uu____6561 :: uu____6568  in
                                         uu____6545 :: uu____6552  in
                                       let uu____6608 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6536
                                         uu____6608
                                        in
                                     let uu____6611 =
                                       let uu____6616 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6616
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6611
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6632 = fresh_a_and_wp ()  in
                                  match uu____6632 with
                                  | (a,wp_sort_a) ->
                                      let uu____6645 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6645 with
                                       | (t,uu____6651) ->
                                           let k =
                                             let uu____6655 =
                                               let uu____6664 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6671 =
                                                 let uu____6680 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6680]  in
                                               uu____6664 :: uu____6671  in
                                             let uu____6705 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6655 uu____6705
                                              in
                                           let trivial =
                                             let uu____6709 =
                                               let uu____6714 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6714 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6709
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6729 =
                                  let uu____6746 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6746 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6775 ->
                                      let repr =
                                        let uu____6779 = fresh_a_and_wp ()
                                           in
                                        match uu____6779 with
                                        | (a,wp_sort_a) ->
                                            let uu____6792 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6792 with
                                             | (t,uu____6798) ->
                                                 let k =
                                                   let uu____6802 =
                                                     let uu____6811 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6818 =
                                                       let uu____6827 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6827]  in
                                                     uu____6811 :: uu____6818
                                                      in
                                                   let uu____6852 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6802 uu____6852
                                                    in
                                                 let uu____6855 =
                                                   let uu____6860 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6860
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6855
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6904 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6904 with
                                          | (uu____6911,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6914 =
                                                let uu____6921 =
                                                  let uu____6922 =
                                                    let uu____6939 =
                                                      let uu____6950 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6967 =
                                                        let uu____6978 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6978]  in
                                                      uu____6950 ::
                                                        uu____6967
                                                       in
                                                    (repr2, uu____6939)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6922
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6921
                                                 in
                                              uu____6914
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7044 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7044 wp  in
                                        let destruct_repr t =
                                          let uu____7059 =
                                            let uu____7060 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7060.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7059 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7071,(t1,uu____7073)::
                                               (wp,uu____7075)::[])
                                              -> (t1, wp)
                                          | uu____7134 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7150 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7150
                                              FStar_Util.must
                                             in
                                          let uu____7177 = fresh_a_and_wp ()
                                             in
                                          match uu____7177 with
                                          | (a,uu____7185) ->
                                              let x_a =
                                                let uu____7191 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7191
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7199 =
                                                    let uu____7204 =
                                                      let uu____7205 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7205
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7214 =
                                                      let uu____7215 =
                                                        let uu____7224 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7224
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7233 =
                                                        let uu____7244 =
                                                          let uu____7253 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7253
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7244]  in
                                                      uu____7215 ::
                                                        uu____7233
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7204 uu____7214
                                                     in
                                                  uu____7199
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7289 =
                                                  let uu____7298 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7305 =
                                                    let uu____7314 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7314]  in
                                                  uu____7298 :: uu____7305
                                                   in
                                                let uu____7339 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7289 uu____7339
                                                 in
                                              let uu____7342 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7342 with
                                               | (k1,uu____7350,uu____7351)
                                                   ->
                                                   let env1 =
                                                     let uu____7355 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7355
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
                                             let uu____7368 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7368
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7406 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7406
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7407 = fresh_a_and_wp ()
                                              in
                                           match uu____7407 with
                                           | (a,wp_sort_a) ->
                                               let uu____7420 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7420 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7436 =
                                                        let uu____7445 =
                                                          let uu____7452 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7452
                                                           in
                                                        [uu____7445]  in
                                                      let uu____7465 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7436 uu____7465
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
                                                      let uu____7473 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7473
                                                       in
                                                    let wp_g_x =
                                                      let uu____7478 =
                                                        let uu____7483 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7484 =
                                                          let uu____7485 =
                                                            let uu____7494 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7494
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7485]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7483
                                                          uu____7484
                                                         in
                                                      uu____7478
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7525 =
                                                          let uu____7530 =
                                                            let uu____7531 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7531
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7540 =
                                                            let uu____7541 =
                                                              let uu____7544
                                                                =
                                                                let uu____7547
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7548
                                                                  =
                                                                  let uu____7551
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7552
                                                                    =
                                                                    let uu____7555
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7556
                                                                    =
                                                                    let uu____7559
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7559]
                                                                     in
                                                                    uu____7555
                                                                    ::
                                                                    uu____7556
                                                                     in
                                                                  uu____7551
                                                                    ::
                                                                    uu____7552
                                                                   in
                                                                uu____7547 ::
                                                                  uu____7548
                                                                 in
                                                              r :: uu____7544
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7541
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7530
                                                            uu____7540
                                                           in
                                                        uu____7525
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7577 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7577
                                                      then
                                                        let uu____7588 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7595 =
                                                          let uu____7604 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7604]  in
                                                        uu____7588 ::
                                                          uu____7595
                                                      else []  in
                                                    let k =
                                                      let uu____7640 =
                                                        let uu____7649 =
                                                          let uu____7658 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7665 =
                                                            let uu____7674 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7674]  in
                                                          uu____7658 ::
                                                            uu____7665
                                                           in
                                                        let uu____7699 =
                                                          let uu____7708 =
                                                            let uu____7717 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7724 =
                                                              let uu____7733
                                                                =
                                                                let uu____7740
                                                                  =
                                                                  let uu____7741
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7741
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7740
                                                                 in
                                                              let uu____7742
                                                                =
                                                                let uu____7751
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7758
                                                                  =
                                                                  let uu____7767
                                                                    =
                                                                    let uu____7774
                                                                    =
                                                                    let uu____7775
                                                                    =
                                                                    let uu____7784
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7784]
                                                                     in
                                                                    let uu____7803
                                                                    =
                                                                    let uu____7806
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7806
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7775
                                                                    uu____7803
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7774
                                                                     in
                                                                  [uu____7767]
                                                                   in
                                                                uu____7751 ::
                                                                  uu____7758
                                                                 in
                                                              uu____7733 ::
                                                                uu____7742
                                                               in
                                                            uu____7717 ::
                                                              uu____7724
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7708
                                                           in
                                                        FStar_List.append
                                                          uu____7649
                                                          uu____7699
                                                         in
                                                      let uu____7851 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7640 uu____7851
                                                       in
                                                    let uu____7854 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7854 with
                                                     | (k1,uu____7862,uu____7863)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___805_7873
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___805_7873.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7875  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7875)
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
                                              (let uu____7902 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7916 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7916 with
                                                    | (usubst,uvs) ->
                                                        let uu____7939 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7940 =
                                                          let uu___818_7941 =
                                                            act  in
                                                          let uu____7942 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7943 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___818_7941.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___818_7941.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___818_7941.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7942;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7943
                                                          }  in
                                                        (uu____7939,
                                                          uu____7940))
                                                  in
                                               match uu____7902 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7947 =
                                                       let uu____7948 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7948.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7947 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7974 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7974
                                                         then
                                                           let uu____7977 =
                                                             let uu____7980 =
                                                               let uu____7981
                                                                 =
                                                                 let uu____7982
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7982
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7981
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7980
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7977
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____8005 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____8006 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____8006 with
                                                    | (act_typ1,uu____8014,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___835_8017 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___835_8017.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____8020 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____8020
                                                          then
                                                            let uu____8024 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____8026 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____8028 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____8024
                                                              uu____8026
                                                              uu____8028
                                                          else ());
                                                         (let uu____8033 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8033
                                                          with
                                                          | (act_defn,uu____8041,g_a)
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
                                                              let uu____8045
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
                                                                    let uu____8081
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8081
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8093)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8100
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8100
                                                                     in
                                                                    let uu____8103
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8103
                                                                    with
                                                                    | 
                                                                    (k1,uu____8117,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8121
                                                                    ->
                                                                    let uu____8122
                                                                    =
                                                                    let uu____8128
                                                                    =
                                                                    let uu____8130
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8132
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8130
                                                                    uu____8132
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8128)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8122
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8045
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
                                                                    let uu____8150
                                                                    =
                                                                    let uu____8151
                                                                    =
                                                                    let uu____8152
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8152
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8151
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8150);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8154
                                                                    =
                                                                    let uu____8155
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8155.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8154
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8180
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8180
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8187
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8187
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8207
                                                                    =
                                                                    let uu____8208
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8208]
                                                                     in
                                                                    let uu____8209
                                                                    =
                                                                    let uu____8220
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8220]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8207;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8209;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8245
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8245))
                                                                    | 
                                                                    uu____8248
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8250
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8272
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8272))
                                                                     in
                                                                    match uu____8250
                                                                    with
                                                                    | 
                                                                    (univs1,act_defn2)
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
                                                                    univs1
                                                                    act_typ4
                                                                     in
                                                                    let uu___885_8291
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___885_8291.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___885_8291.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___885_8291.FStar_Syntax_Syntax.action_params);
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
                                match uu____6729 with
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
                                      let uu____8334 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8334 ts1
                                       in
                                    let combinators =
                                      {
                                        FStar_Syntax_Syntax.ret_wp = ret_wp;
                                        FStar_Syntax_Syntax.bind_wp = bind_wp;
                                        FStar_Syntax_Syntax.stronger =
                                          stronger;
                                        FStar_Syntax_Syntax.if_then_else =
                                          if_then_else1;
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
                                          uu____8346 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8347 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8348 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___905_8351 = ed2  in
                                      let uu____8352 = cl signature  in
                                      let uu____8353 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___908_8361 = a  in
                                             let uu____8362 =
                                               let uu____8363 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8363
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8388 =
                                               let uu____8389 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8389
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___908_8361.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___908_8361.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___908_8361.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___908_8361.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8362;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8388
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___905_8351.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___905_8351.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___905_8351.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___905_8351.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8352;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8353;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___905_8351.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8415 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8415
                                      then
                                        let uu____8420 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8420
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
        let uu____8446 =
          let uu____8461 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8461 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8446 env ed quals
  
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
        let fail1 uu____8511 =
          let uu____8512 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8518 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8512 uu____8518  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8562)::(wp,uu____8564)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8593 -> fail1 ())
        | uu____8594 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8607 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8607
       then
         let uu____8612 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8612
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8629 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8629.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____8641 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8645 =
                let uu____8646 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8646 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8645
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8655 =
                   let uu____8656 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8656 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8655
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8664 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8664))
           in
        if uu____8641
        then
          let uu____8667 =
            let uu____8673 =
              let uu____8675 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8678 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8675 uu____8678
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8673)  in
          FStar_Errors.raise_error uu____8667 r
        else ());
       (let uu____8685 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8685 with
        | (us,lift,lift_ty) ->
            ((let uu____8699 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8699
              then
                let uu____8704 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8710 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8704 uu____8710
              else ());
             (let uu____8719 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8719 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____8737 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.source
                         in
                      let uu____8739 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.target
                         in
                      let uu____8741 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____8737 uu____8739 s uu____8741
                       in
                    let uu____8744 =
                      let uu____8751 =
                        let uu____8756 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____8756
                          (fun uu____8773  ->
                             match uu____8773 with
                             | (t,u) ->
                                 let uu____8784 =
                                   let uu____8785 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____8785
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____8784, u))
                         in
                      match uu____8751 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____8804 =
                              let uu____8805 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____8805.FStar_Syntax_Syntax.n  in
                            match uu____8804 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____8817)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____8845 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____8845 with
                                 | (a',uu____8855)::bs1 ->
                                     let uu____8875 =
                                       let uu____8876 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____8876
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____8942 =
                                       let uu____8955 =
                                         let uu____8958 =
                                           let uu____8959 =
                                             let uu____8966 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____8966)  in
                                           FStar_Syntax_Syntax.NT uu____8959
                                            in
                                         [uu____8958]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____8955
                                        in
                                     FStar_All.pipe_right uu____8875
                                       uu____8942)
                            | uu____8981 ->
                                let uu____8982 =
                                  let uu____8988 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____8988)
                                   in
                                FStar_Errors.raise_error uu____8982 r
                             in
                          let uu____9000 =
                            let uu____9011 =
                              let uu____9016 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____9023 =
                                let uu____9024 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____9024
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____9016 r sub1.FStar_Syntax_Syntax.source
                                u_a uu____9023
                               in
                            match uu____9011 with
                            | (f_sort,g) ->
                                let uu____9045 =
                                  let uu____9052 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9052
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9045, g)
                             in
                          (match uu____9000 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9119 =
                                 let uu____9124 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9125 =
                                   let uu____9126 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9126
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9124 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____9125
                                  in
                               (match uu____9119 with
                                | (repr,g_repr) ->
                                    let uu____9143 =
                                      let uu____9148 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9149 =
                                        let uu____9151 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9153 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9151 uu____9153
                                         in
                                      pure_wp_uvar uu____9148 repr uu____9149
                                        r
                                       in
                                    (match uu____9143 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9165 =
                                             let uu____9166 =
                                               let uu____9167 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9167]  in
                                             let uu____9168 =
                                               let uu____9179 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9179]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9166;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9168;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9165
                                            in
                                         let uu____9212 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9215 =
                                           let uu____9216 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9216 guard_wp
                                            in
                                         (uu____9212, uu____9215))))
                       in
                    match uu____8744 with
                    | (k,g_k) ->
                        ((let uu____9226 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9226
                          then
                            let uu____9231 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9231
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9240 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9240
                           then
                             let uu____9245 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9245
                           else ());
                          (let sub2 =
                             let uu___1001_9251 = sub1  in
                             let uu____9252 =
                               let uu____9255 =
                                 let uu____9256 =
                                   let uu____9259 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9259
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9256)  in
                               FStar_Pervasives_Native.Some uu____9255  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1001_9251.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1001_9251.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9252;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9271 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9271
                            then
                              let uu____9276 =
                                FStar_Syntax_Print.sub_eff_to_string sub2  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9276
                            else ());
                           sub2)))))))))
  
let (tc_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff ->
      FStar_Range.range -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env  ->
    fun sub1  ->
      fun r  ->
        let check_and_gen1 env1 t k =
          let uu____9313 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9313  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9316 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9316
        then tc_layered_lift env sub1
        else
          (let uu____9323 =
             let uu____9330 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9330
              in
           match uu____9323 with
           | (a,wp_a_src) ->
               let uu____9337 =
                 let uu____9344 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9344
                  in
               (match uu____9337 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9352 =
                        let uu____9355 =
                          let uu____9356 =
                            let uu____9363 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9363)  in
                          FStar_Syntax_Syntax.NT uu____9356  in
                        [uu____9355]  in
                      FStar_Syntax_Subst.subst uu____9352 wp_b_tgt  in
                    let expected_k =
                      let uu____9371 =
                        let uu____9380 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9387 =
                          let uu____9396 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9396]  in
                        uu____9380 :: uu____9387  in
                      let uu____9421 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9371 uu____9421  in
                    let repr_type eff_name a1 wp =
                      (let uu____9443 =
                         let uu____9445 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9445  in
                       if uu____9443
                       then
                         let uu____9448 =
                           let uu____9454 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9454)
                            in
                         let uu____9458 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9448 uu____9458
                       else ());
                      (let uu____9461 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9461 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9494 =
                               let uu____9495 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9495
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9494
                              in
                           let uu____9502 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9503 =
                             let uu____9510 =
                               let uu____9511 =
                                 let uu____9528 =
                                   let uu____9539 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9548 =
                                     let uu____9559 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9559]  in
                                   uu____9539 :: uu____9548  in
                                 (repr, uu____9528)  in
                               FStar_Syntax_Syntax.Tm_app uu____9511  in
                             FStar_Syntax_Syntax.mk uu____9510  in
                           uu____9503 FStar_Pervasives_Native.None uu____9502)
                       in
                    let uu____9604 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9777 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9788 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9788 with
                              | (usubst,uvs1) ->
                                  let uu____9811 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9812 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9811, uu____9812)
                            else (env, lift_wp)  in
                          (match uu____9777 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9862 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9862))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9933 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9948 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9948 with
                              | (usubst,uvs) ->
                                  let uu____9973 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9973)
                            else ([], lift)  in
                          (match uu____9933 with
                           | (uvs,lift1) ->
                               ((let uu____10009 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____10009
                                 then
                                   let uu____10013 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____10013
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____10019 =
                                   let uu____10026 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____10026 lift1
                                    in
                                 match uu____10019 with
                                 | (lift2,comp,uu____10051) ->
                                     let uu____10052 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10052 with
                                      | (uu____10081,lift_wp,lift_elab) ->
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
                                            let uu____10113 =
                                              let uu____10124 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10124
                                               in
                                            let uu____10141 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10113, uu____10141)
                                          else
                                            (let uu____10170 =
                                               let uu____10181 =
                                                 let uu____10190 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10190)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10181
                                                in
                                             let uu____10205 =
                                               let uu____10214 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10214)  in
                                             (uu____10170, uu____10205))))))
                       in
                    (match uu____9604 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1085_10278 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1085_10278.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1085_10278.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1085_10278.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1085_10278.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1085_10278.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1085_10278.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1085_10278.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1085_10278.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1085_10278.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1085_10278.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1085_10278.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1085_10278.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1085_10278.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1085_10278.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1085_10278.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1085_10278.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1085_10278.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1085_10278.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1085_10278.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1085_10278.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1085_10278.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1085_10278.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1085_10278.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1085_10278.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1085_10278.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1085_10278.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1085_10278.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1085_10278.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1085_10278.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1085_10278.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1085_10278.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1085_10278.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1085_10278.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1085_10278.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1085_10278.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1085_10278.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1085_10278.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1085_10278.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1085_10278.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1085_10278.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1085_10278.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1085_10278.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1085_10278.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1085_10278.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1085_10278.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10311 =
                                 let uu____10316 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10316 with
                                 | (usubst,uvs1) ->
                                     let uu____10339 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10340 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10339, uu____10340)
                                  in
                               (match uu____10311 with
                                | (env2,lift2) ->
                                    let uu____10345 =
                                      let uu____10352 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10352
                                       in
                                    (match uu____10345 with
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
                                             sub1.FStar_Syntax_Syntax.source
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
                                             let uu____10378 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10379 =
                                               let uu____10386 =
                                                 let uu____10387 =
                                                   let uu____10404 =
                                                     let uu____10415 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10424 =
                                                       let uu____10435 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10435]  in
                                                     uu____10415 ::
                                                       uu____10424
                                                      in
                                                   (lift_wp1, uu____10404)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10387
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10386
                                                in
                                             uu____10379
                                               FStar_Pervasives_Native.None
                                               uu____10378
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10483 =
                                             let uu____10492 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10499 =
                                               let uu____10508 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10515 =
                                                 let uu____10524 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10524]  in
                                               uu____10508 :: uu____10515  in
                                             uu____10492 :: uu____10499  in
                                           let uu____10555 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10483 uu____10555
                                            in
                                         let uu____10558 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10558 with
                                          | (expected_k2,uu____10568,uu____10569)
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
                                                   let uu____10577 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10577))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10585 =
                             let uu____10587 =
                               let uu____10589 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10589
                                 FStar_List.length
                                in
                             uu____10587 <> Prims.int_one  in
                           if uu____10585
                           then
                             let uu____10612 =
                               let uu____10618 =
                                 let uu____10620 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10622 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10624 =
                                   let uu____10626 =
                                     let uu____10628 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10628
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10626
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10620 uu____10622 uu____10624
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10618)
                                in
                             FStar_Errors.raise_error uu____10612 r
                           else ());
                          (let uu____10655 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10658 =
                                  let uu____10660 =
                                    let uu____10663 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10663
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10660
                                    FStar_List.length
                                   in
                                uu____10658 <> Prims.int_one)
                              in
                           if uu____10655
                           then
                             let uu____10702 =
                               let uu____10708 =
                                 let uu____10710 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10712 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10714 =
                                   let uu____10716 =
                                     let uu____10718 =
                                       let uu____10721 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10721
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10718
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10716
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10710 uu____10712 uu____10714
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10708)
                                in
                             FStar_Errors.raise_error uu____10702 r
                           else ());
                          (let uu___1122_10763 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1122_10763.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1122_10763.FStar_Syntax_Syntax.target);
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
    fun uu____10794  ->
      fun r  ->
        match uu____10794 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10817 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10845 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10845 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10876 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10876 c  in
                     let uu____10885 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10885, uvs1, tps1, c1))
               in
            (match uu____10817 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10905 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10905 with
                  | (tps2,c2) ->
                      let uu____10920 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10920 with
                       | (tps3,env3,us) ->
                           let uu____10938 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10938 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10964)::uu____10965 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10984 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10992 =
                                    let uu____10994 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10994  in
                                  if uu____10992
                                  then
                                    let uu____10997 =
                                      let uu____11003 =
                                        let uu____11005 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____11007 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____11005 uu____11007
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____11003)
                                       in
                                    FStar_Errors.raise_error uu____10997 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____11015 =
                                    let uu____11016 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____11016
                                     in
                                  match uu____11015 with
                                  | (uvs2,t) ->
                                      let uu____11045 =
                                        let uu____11050 =
                                          let uu____11063 =
                                            let uu____11064 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11064.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11063)  in
                                        match uu____11050 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11079,c5)) -> ([], c5)
                                        | (uu____11121,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11160 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11045 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11192 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11192 with
                                               | (uu____11197,t1) ->
                                                   let uu____11199 =
                                                     let uu____11205 =
                                                       let uu____11207 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11209 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11213 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11207
                                                         uu____11209
                                                         uu____11213
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11205)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11199 r)
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
      fun n1  ->
        fun p  ->
          fun ts  ->
            let eff_name =
              let uu____11255 = FStar_Ident.string_of_lid m  in
              let uu____11257 = FStar_Ident.string_of_lid n1  in
              let uu____11259 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11255 uu____11257
                uu____11259
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            (let uu____11268 =
               FStar_TypeChecker_Env.is_user_reifiable_effect env p  in
             if uu____11268
             then
               let uu____11271 =
                 let uu____11277 =
                   let uu____11279 = FStar_Ident.string_of_lid p  in
                   FStar_Util.format2
                     "Error typechecking the polymonadic bind %s, the final effect %s is reifiable and reification of polymondic binds is not yet implemented"
                     eff_name uu____11279
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____11277)  in
               FStar_Errors.raise_error uu____11271 r
             else ());
            (let uu____11285 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts
                in
             match uu____11285 with
             | (us,t,ty) ->
                 let uu____11301 = FStar_Syntax_Subst.open_univ_vars us ty
                    in
                 (match uu____11301 with
                  | (us1,ty1) ->
                      let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                         in
                      (check_no_subtyping_for_layered_combinator env1 ty1
                         FStar_Pervasives_Native.None;
                       (let uu____11314 =
                          let uu____11319 = FStar_Syntax_Util.type_u ()  in
                          FStar_All.pipe_right uu____11319
                            (fun uu____11336  ->
                               match uu____11336 with
                               | (t1,u) ->
                                   let uu____11347 =
                                     let uu____11348 =
                                       FStar_Syntax_Syntax.gen_bv "a"
                                         FStar_Pervasives_Native.None t1
                                        in
                                     FStar_All.pipe_right uu____11348
                                       FStar_Syntax_Syntax.mk_binder
                                      in
                                   (uu____11347, u))
                           in
                        match uu____11314 with
                        | (a,u_a) ->
                            let uu____11356 =
                              let uu____11361 = FStar_Syntax_Util.type_u ()
                                 in
                              FStar_All.pipe_right uu____11361
                                (fun uu____11378  ->
                                   match uu____11378 with
                                   | (t1,u) ->
                                       let uu____11389 =
                                         let uu____11390 =
                                           FStar_Syntax_Syntax.gen_bv "b"
                                             FStar_Pervasives_Native.None t1
                                            in
                                         FStar_All.pipe_right uu____11390
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____11389, u))
                               in
                            (match uu____11356 with
                             | (b,u_b) ->
                                 let rest_bs =
                                   let uu____11407 =
                                     let uu____11408 =
                                       FStar_Syntax_Subst.compress ty1  in
                                     uu____11408.FStar_Syntax_Syntax.n  in
                                   match uu____11407 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____11420) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (4))
                                       ->
                                       let uu____11448 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____11448 with
                                        | (a',uu____11458)::(b',uu____11460)::bs1
                                            ->
                                            let uu____11490 =
                                              let uu____11491 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - (Prims.of_int (2))))
                                                 in
                                              FStar_All.pipe_right
                                                uu____11491
                                                FStar_Pervasives_Native.fst
                                               in
                                            let uu____11557 =
                                              let uu____11570 =
                                                let uu____11573 =
                                                  let uu____11574 =
                                                    let uu____11581 =
                                                      let uu____11584 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____11584
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    (a', uu____11581)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____11574
                                                   in
                                                let uu____11597 =
                                                  let uu____11600 =
                                                    let uu____11601 =
                                                      let uu____11608 =
                                                        let uu____11611 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____11611
                                                          FStar_Syntax_Syntax.bv_to_name
                                                         in
                                                      (b', uu____11608)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____11601
                                                     in
                                                  [uu____11600]  in
                                                uu____11573 :: uu____11597
                                                 in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____11570
                                               in
                                            FStar_All.pipe_right uu____11490
                                              uu____11557)
                                   | uu____11632 ->
                                       let uu____11633 =
                                         let uu____11639 =
                                           let uu____11641 =
                                             FStar_Syntax_Print.tag_of_term
                                               ty1
                                              in
                                           let uu____11643 =
                                             FStar_Syntax_Print.term_to_string
                                               ty1
                                              in
                                           FStar_Util.format3
                                             "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                             eff_name uu____11641 uu____11643
                                            in
                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                           uu____11639)
                                          in
                                       FStar_Errors.raise_error uu____11633 r
                                    in
                                 let bs = a :: b :: rest_bs  in
                                 let uu____11676 =
                                   let uu____11687 =
                                     let uu____11692 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs
                                        in
                                     let uu____11693 =
                                       let uu____11694 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____11694
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     FStar_TypeChecker_Util.fresh_effect_repr_en
                                       uu____11692 r m u_a uu____11693
                                      in
                                   match uu____11687 with
                                   | (repr,g) ->
                                       let uu____11715 =
                                         let uu____11722 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr
                                            in
                                         FStar_All.pipe_right uu____11722
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____11715, g)
                                    in
                                 (match uu____11676 with
                                  | (f,guard_f) ->
                                      let uu____11754 =
                                        let x_a =
                                          let uu____11772 =
                                            let uu____11773 =
                                              let uu____11774 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11774
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x"
                                              FStar_Pervasives_Native.None
                                              uu____11773
                                             in
                                          FStar_All.pipe_right uu____11772
                                            FStar_Syntax_Syntax.mk_binder
                                           in
                                        let uu____11790 =
                                          let uu____11795 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1
                                              (FStar_List.append bs [x_a])
                                             in
                                          let uu____11814 =
                                            let uu____11815 =
                                              FStar_All.pipe_right b
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_All.pipe_right uu____11815
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          FStar_TypeChecker_Util.fresh_effect_repr_en
                                            uu____11795 r n1 u_b uu____11814
                                           in
                                        match uu____11790 with
                                        | (repr,g) ->
                                            let uu____11836 =
                                              let uu____11843 =
                                                let uu____11844 =
                                                  let uu____11845 =
                                                    let uu____11848 =
                                                      let uu____11851 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          ()
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____11851
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      repr uu____11848
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    [x_a] uu____11845
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "g"
                                                  FStar_Pervasives_Native.None
                                                  uu____11844
                                                 in
                                              FStar_All.pipe_right
                                                uu____11843
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____11836, g)
                                         in
                                      (match uu____11754 with
                                       | (g,guard_g) ->
                                           let uu____11895 =
                                             let uu____11900 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs
                                                in
                                             let uu____11901 =
                                               let uu____11902 =
                                                 FStar_All.pipe_right b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11902
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               uu____11900 r p u_b
                                               uu____11901
                                              in
                                           (match uu____11895 with
                                            | (repr,guard_repr) ->
                                                let uu____11917 =
                                                  let uu____11922 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env1 bs
                                                     in
                                                  let uu____11923 =
                                                    FStar_Util.format1
                                                      "implicit for pure_wp in checking %s"
                                                      eff_name
                                                     in
                                                  pure_wp_uvar uu____11922
                                                    repr uu____11923 r
                                                   in
                                                (match uu____11917 with
                                                 | (pure_wp_uvar1,g_pure_wp_uvar)
                                                     ->
                                                     let k =
                                                       let uu____11935 =
                                                         let uu____11938 =
                                                           let uu____11939 =
                                                             let uu____11940
                                                               =
                                                               FStar_TypeChecker_Env.new_u_univ
                                                                 ()
                                                                in
                                                             [uu____11940]
                                                              in
                                                           let uu____11941 =
                                                             let uu____11952
                                                               =
                                                               FStar_All.pipe_right
                                                                 pure_wp_uvar1
                                                                 FStar_Syntax_Syntax.as_arg
                                                                in
                                                             [uu____11952]
                                                              in
                                                           {
                                                             FStar_Syntax_Syntax.comp_univs
                                                               = uu____11939;
                                                             FStar_Syntax_Syntax.effect_name
                                                               =
                                                               FStar_Parser_Const.effect_PURE_lid;
                                                             FStar_Syntax_Syntax.result_typ
                                                               = repr;
                                                             FStar_Syntax_Syntax.effect_args
                                                               = uu____11941;
                                                             FStar_Syntax_Syntax.flags
                                                               = []
                                                           }  in
                                                         FStar_Syntax_Syntax.mk_Comp
                                                           uu____11938
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____11935
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
                                                      (let uu____12012 =
                                                         FStar_All.pipe_left
                                                           (FStar_TypeChecker_Env.debug
                                                              env1)
                                                           FStar_Options.Extreme
                                                          in
                                                       if uu____12012
                                                       then
                                                         let uu____12016 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             (us1, t)
                                                            in
                                                         let uu____12022 =
                                                           FStar_Syntax_Print.tscheme_to_string
                                                             (us1, k)
                                                            in
                                                         FStar_Util.print3
                                                           "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                           eff_name
                                                           uu____12016
                                                           uu____12022
                                                       else ());
                                                      (let uu____12032 =
                                                         let uu____12038 =
                                                           FStar_Util.format1
                                                             "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                             eff_name
                                                            in
                                                         (FStar_Errors.Warning_BleedingEdge_Feature,
                                                           uu____12038)
                                                          in
                                                       FStar_Errors.log_issue
                                                         r uu____12032);
                                                      (let uu____12042 =
                                                         let uu____12043 =
                                                           let uu____12046 =
                                                             FStar_All.pipe_right
                                                               k
                                                               (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                  env1)
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____12046
                                                             (FStar_Syntax_Subst.close_univ_vars
                                                                us1)
                                                            in
                                                         (us1, uu____12043)
                                                          in
                                                       ((us1, t),
                                                         uu____12042))))))))))))
  