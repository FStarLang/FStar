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
                   let uu____1647 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1647 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1671 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1671 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            (check_no_subtyping_for_layered_combinator env ty
                               FStar_Pervasives_Native.None;
                             (let uu____1692 = fresh_a_and_u_a "a"  in
                              match uu____1692 with
                              | (a,u_a) ->
                                  let uu____1712 = fresh_a_and_u_a "b"  in
                                  (match uu____1712 with
                                   | (b,u_b) ->
                                       let rest_bs =
                                         let uu____1741 =
                                           let uu____1742 =
                                             FStar_Syntax_Subst.compress ty
                                              in
                                           uu____1742.FStar_Syntax_Syntax.n
                                            in
                                         match uu____1741 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____1754) when
                                             (FStar_List.length bs) >=
                                               (Prims.of_int (4))
                                             ->
                                             let uu____1782 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             (match uu____1782 with
                                              | (a',uu____1792)::(b',uu____1794)::bs1
                                                  ->
                                                  let uu____1824 =
                                                    let uu____1825 =
                                                      FStar_All.pipe_right
                                                        bs1
                                                        (FStar_List.splitAt
                                                           ((FStar_List.length
                                                               bs1)
                                                              -
                                                              (Prims.of_int (2))))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____1825
                                                      FStar_Pervasives_Native.fst
                                                     in
                                                  let uu____1891 =
                                                    let uu____1904 =
                                                      let uu____1907 =
                                                        let uu____1908 =
                                                          let uu____1915 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              (FStar_Pervasives_Native.fst
                                                                 a)
                                                             in
                                                          (a', uu____1915)
                                                           in
                                                        FStar_Syntax_Syntax.NT
                                                          uu____1908
                                                         in
                                                      let uu____1922 =
                                                        let uu____1925 =
                                                          let uu____1926 =
                                                            let uu____1933 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                (FStar_Pervasives_Native.fst
                                                                   b)
                                                               in
                                                            (b', uu____1933)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____1926
                                                           in
                                                        [uu____1925]  in
                                                      uu____1907 ::
                                                        uu____1922
                                                       in
                                                    FStar_Syntax_Subst.subst_binders
                                                      uu____1904
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____1824 uu____1891)
                                         | uu____1948 ->
                                             not_an_arrow_error "bind"
                                               (Prims.of_int (4)) ty r
                                          in
                                       let bs = a :: b :: rest_bs  in
                                       let uu____1972 =
                                         let uu____1983 =
                                           let uu____1988 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____1989 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____1988 u_a
                                             uu____1989
                                            in
                                         match uu____1983 with
                                         | (repr1,g) ->
                                             let uu____2004 =
                                               let uu____2011 =
                                                 FStar_Syntax_Syntax.gen_bv
                                                   "f"
                                                   FStar_Pervasives_Native.None
                                                   repr1
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2011
                                                 FStar_Syntax_Syntax.mk_binder
                                                in
                                             (uu____2004, g)
                                          in
                                       (match uu____1972 with
                                        | (f,guard_f) ->
                                            let uu____2051 =
                                              let x_a = fresh_x_a "x" a  in
                                              let uu____2064 =
                                                let uu____2069 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env
                                                    (FStar_List.append bs
                                                       [x_a])
                                                   in
                                                let uu____2088 =
                                                  FStar_All.pipe_right
                                                    (FStar_Pervasives_Native.fst
                                                       b)
                                                    FStar_Syntax_Syntax.bv_to_name
                                                   in
                                                fresh_repr r uu____2069 u_b
                                                  uu____2088
                                                 in
                                              match uu____2064 with
                                              | (repr1,g) ->
                                                  let uu____2103 =
                                                    let uu____2110 =
                                                      let uu____2111 =
                                                        let uu____2112 =
                                                          let uu____2115 =
                                                            let uu____2118 =
                                                              FStar_TypeChecker_Env.new_u_univ
                                                                ()
                                                               in
                                                            FStar_Pervasives_Native.Some
                                                              uu____2118
                                                             in
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1 uu____2115
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          [x_a] uu____2112
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "g"
                                                        FStar_Pervasives_Native.None
                                                        uu____2111
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____2110
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  (uu____2103, g)
                                               in
                                            (match uu____2051 with
                                             | (g,guard_g) ->
                                                 let uu____2170 =
                                                   let uu____2175 =
                                                     FStar_TypeChecker_Env.push_binders
                                                       env bs
                                                      in
                                                   let uu____2176 =
                                                     FStar_All.pipe_right
                                                       (FStar_Pervasives_Native.fst
                                                          b)
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   fresh_repr r uu____2175
                                                     u_b uu____2176
                                                    in
                                                 (match uu____2170 with
                                                  | (repr1,guard_repr) ->
                                                      let k =
                                                        let uu____2196 =
                                                          FStar_Syntax_Syntax.mk_Total'
                                                            repr1
                                                            (FStar_Pervasives_Native.Some
                                                               u_b)
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          (FStar_List.append
                                                             bs [f; g])
                                                          uu____2196
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
                                                         guard_eq];
                                                       (let uu____2225 =
                                                          let uu____2228 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2228
                                                            (FStar_Syntax_Subst.close_univ_vars
                                                               bind_us)
                                                           in
                                                        (bind_us, bind_t,
                                                          uu____2225))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2257 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2257 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2285 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2285 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2310 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2310
                          then
                            let uu____2315 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2321 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2315 uu____2321
                          else ());
                         (let uu____2330 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2330 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              (check_no_subtyping_for_layered_combinator env
                                 ty FStar_Pervasives_Native.None;
                               (let uu____2351 = fresh_a_and_u_a "a"  in
                                match uu____2351 with
                                | (a,u) ->
                                    let rest_bs =
                                      let uu____2380 =
                                        let uu____2381 =
                                          FStar_Syntax_Subst.compress ty  in
                                        uu____2381.FStar_Syntax_Syntax.n  in
                                      match uu____2380 with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs,uu____2393) when
                                          (FStar_List.length bs) >=
                                            (Prims.of_int (2))
                                          ->
                                          let uu____2421 =
                                            FStar_Syntax_Subst.open_binders
                                              bs
                                             in
                                          (match uu____2421 with
                                           | (a',uu____2431)::bs1 ->
                                               let uu____2451 =
                                                 let uu____2452 =
                                                   FStar_All.pipe_right bs1
                                                     (FStar_List.splitAt
                                                        ((FStar_List.length
                                                            bs1)
                                                           - Prims.int_one))
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____2452
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               let uu____2550 =
                                                 let uu____2563 =
                                                   let uu____2566 =
                                                     let uu____2567 =
                                                       let uu____2574 =
                                                         FStar_Syntax_Syntax.bv_to_name
                                                           (FStar_Pervasives_Native.fst
                                                              a)
                                                          in
                                                       (a', uu____2574)  in
                                                     FStar_Syntax_Syntax.NT
                                                       uu____2567
                                                      in
                                                   [uu____2566]  in
                                                 FStar_Syntax_Subst.subst_binders
                                                   uu____2563
                                                  in
                                               FStar_All.pipe_right
                                                 uu____2451 uu____2550)
                                      | uu____2589 ->
                                          not_an_arrow_error "stronger"
                                            (Prims.of_int (2)) ty r
                                       in
                                    let bs = a :: rest_bs  in
                                    let uu____2607 =
                                      let uu____2618 =
                                        let uu____2623 =
                                          FStar_TypeChecker_Env.push_binders
                                            env bs
                                           in
                                        let uu____2624 =
                                          FStar_All.pipe_right
                                            (FStar_Pervasives_Native.fst a)
                                            FStar_Syntax_Syntax.bv_to_name
                                           in
                                        fresh_repr r uu____2623 u uu____2624
                                         in
                                      match uu____2618 with
                                      | (repr1,g) ->
                                          let uu____2639 =
                                            let uu____2646 =
                                              FStar_Syntax_Syntax.gen_bv "f"
                                                FStar_Pervasives_Native.None
                                                repr1
                                               in
                                            FStar_All.pipe_right uu____2646
                                              FStar_Syntax_Syntax.mk_binder
                                             in
                                          (uu____2639, g)
                                       in
                                    (match uu____2607 with
                                     | (f,guard_f) ->
                                         let uu____2686 =
                                           let uu____2691 =
                                             FStar_TypeChecker_Env.push_binders
                                               env bs
                                              in
                                           let uu____2692 =
                                             FStar_All.pipe_right
                                               (FStar_Pervasives_Native.fst a)
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           fresh_repr r uu____2691 u
                                             uu____2692
                                            in
                                         (match uu____2686 with
                                          | (ret_t,guard_ret_t) ->
                                              let uu____2709 =
                                                let uu____2714 =
                                                  FStar_TypeChecker_Env.push_binders
                                                    env bs
                                                   in
                                                let uu____2715 =
                                                  FStar_Util.format1
                                                    "implicit for pure_wp in checking stronger for %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   in
                                                pure_wp_uvar uu____2714 ret_t
                                                  uu____2715 r
                                                 in
                                              (match uu____2709 with
                                               | (pure_wp_uvar1,guard_wp) ->
                                                   let c =
                                                     let uu____2733 =
                                                       let uu____2734 =
                                                         let uu____2735 =
                                                           FStar_TypeChecker_Env.new_u_univ
                                                             ()
                                                            in
                                                         [uu____2735]  in
                                                       let uu____2736 =
                                                         let uu____2747 =
                                                           FStar_All.pipe_right
                                                             pure_wp_uvar1
                                                             FStar_Syntax_Syntax.as_arg
                                                            in
                                                         [uu____2747]  in
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____2734;
                                                         FStar_Syntax_Syntax.effect_name
                                                           =
                                                           FStar_Parser_Const.effect_PURE_lid;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = ret_t;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____2736;
                                                         FStar_Syntax_Syntax.flags
                                                           = []
                                                       }  in
                                                     FStar_Syntax_Syntax.mk_Comp
                                                       uu____2733
                                                      in
                                                   let k =
                                                     FStar_Syntax_Util.arrow
                                                       (FStar_List.append bs
                                                          [f]) c
                                                      in
                                                   ((let uu____2802 =
                                                       FStar_All.pipe_left
                                                         (FStar_TypeChecker_Env.debug
                                                            env)
                                                         (FStar_Options.Other
                                                            "LayeredEffects")
                                                        in
                                                     if uu____2802
                                                     then
                                                       let uu____2807 =
                                                         FStar_Syntax_Print.term_to_string
                                                           k
                                                          in
                                                       FStar_Util.print1
                                                         "Expected type before unification: %s\n"
                                                         uu____2807
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
                                                     (let uu____2814 =
                                                        let uu____2817 =
                                                          let uu____2818 =
                                                            FStar_All.pipe_right
                                                              k
                                                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____2818
                                                            (FStar_TypeChecker_Normalize.normalize
                                                               [FStar_TypeChecker_Env.Beta;
                                                               FStar_TypeChecker_Env.Eager_unfolding]
                                                               env)
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____2817
                                                          (FStar_Syntax_Subst.close_univ_vars
                                                             stronger_us)
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2814)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2847 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2847 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2875 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2875 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2899 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2899 with
                          | (us,t) ->
                              let uu____2918 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2918 with
                               | (uu____2935,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   (check_no_subtyping_for_layered_combinator
                                      env t (FStar_Pervasives_Native.Some ty);
                                    (let uu____2939 = fresh_a_and_u_a "a"  in
                                     match uu____2939 with
                                     | (a,u_a) ->
                                         let rest_bs =
                                           let uu____2968 =
                                             let uu____2969 =
                                               FStar_Syntax_Subst.compress ty
                                                in
                                             uu____2969.FStar_Syntax_Syntax.n
                                              in
                                           match uu____2968 with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs,uu____2981) when
                                               (FStar_List.length bs) >=
                                                 (Prims.of_int (4))
                                               ->
                                               let uu____3009 =
                                                 FStar_Syntax_Subst.open_binders
                                                   bs
                                                  in
                                               (match uu____3009 with
                                                | (a',uu____3019)::bs1 ->
                                                    let uu____3039 =
                                                      let uu____3040 =
                                                        FStar_All.pipe_right
                                                          bs1
                                                          (FStar_List.splitAt
                                                             ((FStar_List.length
                                                                 bs1)
                                                                -
                                                                (Prims.of_int (3))))
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3040
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    let uu____3138 =
                                                      let uu____3151 =
                                                        let uu____3154 =
                                                          let uu____3155 =
                                                            let uu____3162 =
                                                              let uu____3165
                                                                =
                                                                FStar_All.pipe_right
                                                                  a
                                                                  FStar_Pervasives_Native.fst
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____3165
                                                                FStar_Syntax_Syntax.bv_to_name
                                                               in
                                                            (a', uu____3162)
                                                             in
                                                          FStar_Syntax_Syntax.NT
                                                            uu____3155
                                                           in
                                                        [uu____3154]  in
                                                      FStar_Syntax_Subst.subst_binders
                                                        uu____3151
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3039 uu____3138)
                                           | uu____3186 ->
                                               not_an_arrow_error
                                                 "if_then_else"
                                                 (Prims.of_int (4)) ty r
                                            in
                                         let bs = a :: rest_bs  in
                                         let uu____3204 =
                                           let uu____3215 =
                                             let uu____3220 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env bs
                                                in
                                             let uu____3221 =
                                               let uu____3222 =
                                                 FStar_All.pipe_right a
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____3222
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             fresh_repr r uu____3220 u_a
                                               uu____3221
                                              in
                                           match uu____3215 with
                                           | (repr1,g) ->
                                               let uu____3243 =
                                                 let uu____3250 =
                                                   FStar_Syntax_Syntax.gen_bv
                                                     "f"
                                                     FStar_Pervasives_Native.None
                                                     repr1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____3250
                                                   FStar_Syntax_Syntax.mk_binder
                                                  in
                                               (uu____3243, g)
                                            in
                                         (match uu____3204 with
                                          | (f_bs,guard_f) ->
                                              let uu____3290 =
                                                let uu____3301 =
                                                  let uu____3306 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____3307 =
                                                    let uu____3308 =
                                                      FStar_All.pipe_right a
                                                        FStar_Pervasives_Native.fst
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3308
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____3306 u_a
                                                    uu____3307
                                                   in
                                                match uu____3301 with
                                                | (repr1,g) ->
                                                    let uu____3329 =
                                                      let uu____3336 =
                                                        FStar_Syntax_Syntax.gen_bv
                                                          "g"
                                                          FStar_Pervasives_Native.None
                                                          repr1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3336
                                                        FStar_Syntax_Syntax.mk_binder
                                                       in
                                                    (uu____3329, g)
                                                 in
                                              (match uu____3290 with
                                               | (g_bs,guard_g) ->
                                                   let p_b =
                                                     let uu____3383 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "p"
                                                         FStar_Pervasives_Native.None
                                                         FStar_Syntax_Util.ktype0
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3383
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   let uu____3391 =
                                                     let uu____3396 =
                                                       FStar_TypeChecker_Env.push_binders
                                                         env
                                                         (FStar_List.append
                                                            bs [p_b])
                                                        in
                                                     let uu____3415 =
                                                       let uu____3416 =
                                                         FStar_All.pipe_right
                                                           a
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____3416
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     fresh_repr r uu____3396
                                                       u_a uu____3415
                                                      in
                                                   (match uu____3391 with
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
                                                         (let uu____3476 =
                                                            let uu____3479 =
                                                              FStar_All.pipe_right
                                                                k
                                                                (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                   env)
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____3479
                                                              (FStar_Syntax_Subst.close_univ_vars
                                                                 if_then_else_us)
                                                             in
                                                          (if_then_else_us,
                                                            uu____3476,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3492 =
                        let uu____3495 =
                          let uu____3504 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3504 FStar_Util.must  in
                        FStar_All.pipe_right uu____3495
                          FStar_Pervasives_Native.snd
                         in
                      uu____3492.FStar_Syntax_Syntax.pos  in
                    let uu____3533 = if_then_else1  in
                    match uu____3533 with
                    | (ite_us,ite_t,uu____3548) ->
                        let uu____3561 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3561 with
                         | (us,ite_t1) ->
                             let uu____3568 =
                               let uu____3581 =
                                 let uu____3582 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3582.FStar_Syntax_Syntax.n  in
                               match uu____3581 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3598,uu____3599) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3625 =
                                     let uu____3632 =
                                       let uu____3635 =
                                         let uu____3638 =
                                           let uu____3647 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3647
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3638
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3635
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3632
                                       (fun l  ->
                                          let uu____3791 = l  in
                                          match uu____3791 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3625 with
                                    | (f,g,p) ->
                                        let uu____3818 =
                                          let uu____3819 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3819 bs1
                                           in
                                        let uu____3820 =
                                          let uu____3821 =
                                            let uu____3826 =
                                              let uu____3827 =
                                                let uu____3830 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3830
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3827
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3826
                                             in
                                          uu____3821
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3818, uu____3820, f, g, p))
                               | uu____3859 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3568 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3882 =
                                    let uu____3891 = stronger_repr  in
                                    match uu____3891 with
                                    | (uu____3912,subcomp_t,subcomp_ty) ->
                                        let uu____3927 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3927 with
                                         | (uu____3940,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3951 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3951 with
                                               | (uu____3964,subcomp_ty1) ->
                                                   let uu____3966 =
                                                     let uu____3967 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3967.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3966 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3979) ->
                                                        let uu____4000 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____4000
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4106 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4124 =
                                                 let uu____4129 =
                                                   let uu____4130 =
                                                     let uu____4133 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4153 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4133 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4130
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4129
                                                  in
                                               uu____4124
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4162 = aux f_t  in
                                             let uu____4165 = aux g_t  in
                                             (uu____4162, uu____4165))
                                     in
                                  (match uu____3882 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4182 =
                                         let aux t =
                                           let uu____4199 =
                                             let uu____4206 =
                                               let uu____4207 =
                                                 let uu____4234 =
                                                   let uu____4251 =
                                                     let uu____4260 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4260
                                                      in
                                                   (uu____4251,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4234,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4207
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4206
                                              in
                                           uu____4199
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4301 = aux subcomp_f  in
                                         let uu____4302 = aux subcomp_g  in
                                         (uu____4301, uu____4302)  in
                                       (match uu____4182 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4306 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4306
                                              then
                                                let uu____4311 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4313 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4311 uu____4313
                                              else ());
                                             (let uu____4318 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4318 with
                                              | (uu____4325,uu____4326,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4329 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4329 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4331 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4331 with
                                                    | (uu____4338,uu____4339,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4345 =
                                                              let uu____4350
                                                                =
                                                                let uu____4351
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4351
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4352
                                                                =
                                                                let uu____4353
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4353]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4350
                                                                uu____4352
                                                               in
                                                            uu____4345
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4386 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4386 g_g
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
                        (let uu____4410 =
                           let uu____4416 =
                             let uu____4418 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4418
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4416)
                            in
                         FStar_Errors.raise_error uu____4410 r)
                      else ();
                      (let uu____4425 =
                         let uu____4430 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4430 with
                         | (usubst,us) ->
                             let uu____4453 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4454 =
                               let uu___444_4455 = act  in
                               let uu____4456 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4457 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___444_4455.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___444_4455.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___444_4455.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4456;
                                 FStar_Syntax_Syntax.action_typ = uu____4457
                               }  in
                             (uu____4453, uu____4454)
                          in
                       match uu____4425 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4461 =
                               let uu____4462 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4462.FStar_Syntax_Syntax.n  in
                             match uu____4461 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4488 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4488
                                 then
                                   let repr_ts =
                                     let uu____4492 = repr  in
                                     match uu____4492 with
                                     | (us,t,uu____4507) -> (us, t)  in
                                   let repr1 =
                                     let uu____4525 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4525
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4537 =
                                       let uu____4542 =
                                         let uu____4543 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4543 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4542
                                        in
                                     uu____4537 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4561 =
                                       let uu____4564 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4564
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4561
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4567 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4568 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4568 with
                            | (act_typ1,uu____4576,g_t) ->
                                let uu____4578 =
                                  let uu____4585 =
                                    let uu___469_4586 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___469_4586.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___469_4586.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___469_4586.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___469_4586.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___469_4586.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___469_4586.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___469_4586.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___469_4586.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___469_4586.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___469_4586.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___469_4586.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___469_4586.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___469_4586.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___469_4586.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___469_4586.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___469_4586.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.use_eq_strict =
                                        (uu___469_4586.FStar_TypeChecker_Env.use_eq_strict);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___469_4586.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___469_4586.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___469_4586.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___469_4586.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___469_4586.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___469_4586.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___469_4586.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___469_4586.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___469_4586.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___469_4586.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___469_4586.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___469_4586.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___469_4586.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___469_4586.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___469_4586.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___469_4586.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___469_4586.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___469_4586.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___469_4586.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___469_4586.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___469_4586.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___469_4586.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___469_4586.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___469_4586.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___469_4586.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___469_4586.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___469_4586.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___469_4586.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4585
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4578 with
                                 | (act_defn,uu____4589,g_d) ->
                                     ((let uu____4592 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4592
                                       then
                                         let uu____4597 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4599 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4597 uu____4599
                                       else ());
                                      (let uu____4604 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4612 =
                                           let uu____4613 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4613.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4612 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4623) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4646 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4646 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4662 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4662 with
                                                   | (a_tm,uu____4682,g_tm)
                                                       ->
                                                       let uu____4696 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4696 with
                                                        | (repr1,g) ->
                                                            let uu____4709 =
                                                              let uu____4712
                                                                =
                                                                let uu____4715
                                                                  =
                                                                  let uu____4718
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4718
                                                                    (
                                                                    fun _4721
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4721)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4715
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4712
                                                               in
                                                            let uu____4722 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4709,
                                                              uu____4722))))
                                         | uu____4725 ->
                                             let uu____4726 =
                                               let uu____4732 =
                                                 let uu____4734 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4734
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4732)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4726 r
                                          in
                                       match uu____4604 with
                                       | (k,g_k) ->
                                           ((let uu____4751 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4751
                                             then
                                               let uu____4756 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4756
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4764 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4764
                                              then
                                                let uu____4769 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4769
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4782 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4782
                                                   in
                                                let repr_args t =
                                                  let uu____4803 =
                                                    let uu____4804 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4804.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4803 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4856 =
                                                        let uu____4857 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4857.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4856 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4866,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4876 ->
                                                           let uu____4877 =
                                                             let uu____4883 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4883)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4877 r)
                                                  | uu____4892 ->
                                                      let uu____4893 =
                                                        let uu____4899 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4899)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4893 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4909 =
                                                  let uu____4910 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4910.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4909 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4935 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4935 with
                                                     | (bs1,c1) ->
                                                         let uu____4942 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4942
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
                                                              let uu____4953
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4953))
                                                | uu____4956 ->
                                                    let uu____4957 =
                                                      let uu____4963 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4963)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4957 r
                                                 in
                                              (let uu____4967 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4967
                                               then
                                                 let uu____4972 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4972
                                               else ());
                                              (let act2 =
                                                 let uu____4978 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4978 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___542_4992 =
                                                         act1  in
                                                       let uu____4993 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___542_4992.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___542_4992.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___542_4992.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4993
                                                       }
                                                     else
                                                       (let uu____4996 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____5003
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____5003
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4996
                                                        then
                                                          let uu___547_5008 =
                                                            act1  in
                                                          let uu____5009 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___547_5008.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___547_5008.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___547_5008.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___547_5008.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5009
                                                          }
                                                        else
                                                          (let uu____5012 =
                                                             let uu____5018 =
                                                               let uu____5020
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5022
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____5020
                                                                 uu____5022
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5018)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5012 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5047 =
                      match uu____5047 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5092 =
                        let uu____5093 = tschemes_of repr  in
                        let uu____5098 = tschemes_of return_repr  in
                        let uu____5103 = tschemes_of bind_repr  in
                        let uu____5108 = tschemes_of stronger_repr  in
                        let uu____5113 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5093;
                          FStar_Syntax_Syntax.l_return = uu____5098;
                          FStar_Syntax_Syntax.l_bind = uu____5103;
                          FStar_Syntax_Syntax.l_subcomp = uu____5108;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5113
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5092  in
                    let uu___556_5118 = ed  in
                    let uu____5119 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___556_5118.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___556_5118.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___556_5118.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___556_5118.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5126 = signature  in
                         match uu____5126 with | (us,t,uu____5141) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5119;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___556_5118.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5179 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5179
         then
           let uu____5184 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5184
         else ());
        (let uu____5190 =
           let uu____5195 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5195 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5219 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5219  in
               let uu____5220 =
                 let uu____5227 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5227 bs  in
               (match uu____5220 with
                | (bs1,uu____5233,uu____5234) ->
                    let uu____5235 =
                      let tmp_t =
                        let uu____5245 =
                          let uu____5248 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5253  ->
                                 FStar_Pervasives_Native.Some _5253)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5248
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5245  in
                      let uu____5254 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5254 with
                      | (us,tmp_t1) ->
                          let uu____5271 =
                            let uu____5272 =
                              let uu____5273 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5273
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5272
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5271)
                       in
                    (match uu____5235 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5310 ->
                              let uu____5313 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5320 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5320 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5313
                              then (us, bs2)
                              else
                                (let uu____5331 =
                                   let uu____5337 =
                                     let uu____5339 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5341 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5339 uu____5341
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5337)
                                    in
                                 let uu____5345 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5331
                                   uu____5345))))
            in
         match uu____5190 with
         | (us,bs) ->
             let ed1 =
               let uu___590_5353 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___590_5353.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___590_5353.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___590_5353.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___590_5353.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___590_5353.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___590_5353.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5354 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5354 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5373 =
                    let uu____5378 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5378  in
                  (match uu____5373 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5399 =
                           match uu____5399 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5419 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5419 t  in
                               let uu____5428 =
                                 let uu____5429 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5429 t1  in
                               (us1, uu____5428)
                            in
                         let uu___604_5434 = ed1  in
                         let uu____5435 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5436 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5437 =
                           FStar_List.map
                             (fun a  ->
                                let uu___607_5445 = a  in
                                let uu____5446 =
                                  let uu____5447 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5447  in
                                let uu____5458 =
                                  let uu____5459 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5459  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___607_5445.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___607_5445.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___607_5445.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___607_5445.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5446;
                                  FStar_Syntax_Syntax.action_typ = uu____5458
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___604_5434.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___604_5434.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___604_5434.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___604_5434.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5435;
                           FStar_Syntax_Syntax.combinators = uu____5436;
                           FStar_Syntax_Syntax.actions = uu____5437;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___604_5434.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5471 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5471
                         then
                           let uu____5476 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5476
                         else ());
                        (let env =
                           let uu____5483 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5483
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5518 k =
                           match uu____5518 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5538 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5538 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5547 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5547 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5548 =
                                            let uu____5555 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5555 t1
                                             in
                                          (match uu____5548 with
                                           | (t2,uu____5557,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5560 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5560 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5576 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5578 =
                                                 let uu____5580 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5580
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5576 uu____5578
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5595 ->
                                               let uu____5596 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5603 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5603 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5596
                                               then (g_us, t3)
                                               else
                                                 (let uu____5614 =
                                                    let uu____5620 =
                                                      let uu____5622 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5624 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5622
                                                        uu____5624
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5620)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5614
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5632 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5632
                          then
                            let uu____5637 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5637
                          else ());
                         (let fresh_a_and_wp uu____5653 =
                            let fail1 t =
                              let uu____5666 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5666
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5682 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5682 with
                            | (uu____5693,signature1) ->
                                let uu____5695 =
                                  let uu____5696 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5696.FStar_Syntax_Syntax.n  in
                                (match uu____5695 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5706) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5735)::(wp,uu____5737)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5766 -> fail1 signature1)
                                 | uu____5767 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5781 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5781
                            then
                              let uu____5786 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5786
                            else ()  in
                          let ret_wp =
                            let uu____5792 = fresh_a_and_wp ()  in
                            match uu____5792 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5808 =
                                    let uu____5817 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5824 =
                                      let uu____5833 =
                                        let uu____5840 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5840
                                         in
                                      [uu____5833]  in
                                    uu____5817 :: uu____5824  in
                                  let uu____5859 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5808
                                    uu____5859
                                   in
                                let uu____5862 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5862
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5876 = fresh_a_and_wp ()  in
                             match uu____5876 with
                             | (a,wp_sort_a) ->
                                 let uu____5889 = fresh_a_and_wp ()  in
                                 (match uu____5889 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5905 =
                                          let uu____5914 =
                                            let uu____5921 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5921
                                             in
                                          [uu____5914]  in
                                        let uu____5934 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5905
                                          uu____5934
                                         in
                                      let k =
                                        let uu____5940 =
                                          let uu____5949 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5956 =
                                            let uu____5965 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5972 =
                                              let uu____5981 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5988 =
                                                let uu____5997 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____6004 =
                                                  let uu____6013 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6013]  in
                                                uu____5997 :: uu____6004  in
                                              uu____5981 :: uu____5988  in
                                            uu____5965 :: uu____5972  in
                                          uu____5949 :: uu____5956  in
                                        let uu____6056 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5940
                                          uu____6056
                                         in
                                      let uu____6059 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6059
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6073 = fresh_a_and_wp ()  in
                              match uu____6073 with
                              | (a,wp_sort_a) ->
                                  let uu____6086 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6086 with
                                   | (t,uu____6092) ->
                                       let k =
                                         let uu____6096 =
                                           let uu____6105 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6112 =
                                             let uu____6121 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6128 =
                                               let uu____6137 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6137]  in
                                             uu____6121 :: uu____6128  in
                                           uu____6105 :: uu____6112  in
                                         let uu____6168 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6096
                                           uu____6168
                                          in
                                       let uu____6171 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6171
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6185 = fresh_a_and_wp ()  in
                               match uu____6185 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6199 =
                                       let uu____6202 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6202
                                        in
                                     let uu____6203 =
                                       let uu____6204 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6204
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6199
                                       uu____6203
                                      in
                                   let k =
                                     let uu____6216 =
                                       let uu____6225 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6232 =
                                         let uu____6241 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6248 =
                                           let uu____6257 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6264 =
                                             let uu____6273 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6273]  in
                                           uu____6257 :: uu____6264  in
                                         uu____6241 :: uu____6248  in
                                       uu____6225 :: uu____6232  in
                                     let uu____6310 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6216
                                       uu____6310
                                      in
                                   let uu____6313 =
                                     let uu____6318 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6318
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6313
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6350 = fresh_a_and_wp ()  in
                                match uu____6350 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6366 =
                                        let uu____6375 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6382 =
                                          let uu____6391 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6391]  in
                                        uu____6375 :: uu____6382  in
                                      let uu____6416 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6366
                                        uu____6416
                                       in
                                    let uu____6419 =
                                      let uu____6424 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6424
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6419
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6440 = fresh_a_and_wp ()  in
                                 match uu____6440 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6454 =
                                         let uu____6457 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6457
                                          in
                                       let uu____6458 =
                                         let uu____6459 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6459
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6454
                                         uu____6458
                                        in
                                     let wp_sort_b_a =
                                       let uu____6471 =
                                         let uu____6480 =
                                           let uu____6487 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6487
                                            in
                                         [uu____6480]  in
                                       let uu____6500 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6471
                                         uu____6500
                                        in
                                     let k =
                                       let uu____6506 =
                                         let uu____6515 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6522 =
                                           let uu____6531 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6538 =
                                             let uu____6547 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6547]  in
                                           uu____6531 :: uu____6538  in
                                         uu____6515 :: uu____6522  in
                                       let uu____6578 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6506
                                         uu____6578
                                        in
                                     let uu____6581 =
                                       let uu____6586 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6586
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6581
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6602 = fresh_a_and_wp ()  in
                                  match uu____6602 with
                                  | (a,wp_sort_a) ->
                                      let uu____6615 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6615 with
                                       | (t,uu____6621) ->
                                           let k =
                                             let uu____6625 =
                                               let uu____6634 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6641 =
                                                 let uu____6650 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6650]  in
                                               uu____6634 :: uu____6641  in
                                             let uu____6675 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6625 uu____6675
                                              in
                                           let trivial =
                                             let uu____6679 =
                                               let uu____6684 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6684 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6679
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6699 =
                                  let uu____6716 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6716 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6745 ->
                                      let repr =
                                        let uu____6749 = fresh_a_and_wp ()
                                           in
                                        match uu____6749 with
                                        | (a,wp_sort_a) ->
                                            let uu____6762 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6762 with
                                             | (t,uu____6768) ->
                                                 let k =
                                                   let uu____6772 =
                                                     let uu____6781 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6788 =
                                                       let uu____6797 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6797]  in
                                                     uu____6781 :: uu____6788
                                                      in
                                                   let uu____6822 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6772 uu____6822
                                                    in
                                                 let uu____6825 =
                                                   let uu____6830 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6830
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6825
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6874 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6874 with
                                          | (uu____6881,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6884 =
                                                let uu____6891 =
                                                  let uu____6892 =
                                                    let uu____6909 =
                                                      let uu____6920 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6937 =
                                                        let uu____6948 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6948]  in
                                                      uu____6920 ::
                                                        uu____6937
                                                       in
                                                    (repr2, uu____6909)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6892
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6891
                                                 in
                                              uu____6884
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7014 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7014 wp  in
                                        let destruct_repr t =
                                          let uu____7029 =
                                            let uu____7030 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7030.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7029 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7041,(t1,uu____7043)::
                                               (wp,uu____7045)::[])
                                              -> (t1, wp)
                                          | uu____7104 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7120 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7120
                                              FStar_Util.must
                                             in
                                          let uu____7147 = fresh_a_and_wp ()
                                             in
                                          match uu____7147 with
                                          | (a,uu____7155) ->
                                              let x_a =
                                                let uu____7161 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7161
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7169 =
                                                    let uu____7174 =
                                                      let uu____7175 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7175
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7184 =
                                                      let uu____7185 =
                                                        let uu____7194 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7194
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7203 =
                                                        let uu____7214 =
                                                          let uu____7223 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7223
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7214]  in
                                                      uu____7185 ::
                                                        uu____7203
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7174 uu____7184
                                                     in
                                                  uu____7169
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7259 =
                                                  let uu____7268 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7275 =
                                                    let uu____7284 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7284]  in
                                                  uu____7268 :: uu____7275
                                                   in
                                                let uu____7309 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7259 uu____7309
                                                 in
                                              let uu____7312 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7312 with
                                               | (k1,uu____7320,uu____7321)
                                                   ->
                                                   let env1 =
                                                     let uu____7325 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7325
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
                                             let uu____7338 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7338
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7376 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7376
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7377 = fresh_a_and_wp ()
                                              in
                                           match uu____7377 with
                                           | (a,wp_sort_a) ->
                                               let uu____7390 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7390 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7406 =
                                                        let uu____7415 =
                                                          let uu____7422 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7422
                                                           in
                                                        [uu____7415]  in
                                                      let uu____7435 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7406 uu____7435
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
                                                      let uu____7443 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7443
                                                       in
                                                    let wp_g_x =
                                                      let uu____7448 =
                                                        let uu____7453 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7454 =
                                                          let uu____7455 =
                                                            let uu____7464 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7464
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7455]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7453
                                                          uu____7454
                                                         in
                                                      uu____7448
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7495 =
                                                          let uu____7500 =
                                                            let uu____7501 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7501
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7510 =
                                                            let uu____7511 =
                                                              let uu____7514
                                                                =
                                                                let uu____7517
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7518
                                                                  =
                                                                  let uu____7521
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7522
                                                                    =
                                                                    let uu____7525
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7526
                                                                    =
                                                                    let uu____7529
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7529]
                                                                     in
                                                                    uu____7525
                                                                    ::
                                                                    uu____7526
                                                                     in
                                                                  uu____7521
                                                                    ::
                                                                    uu____7522
                                                                   in
                                                                uu____7517 ::
                                                                  uu____7518
                                                                 in
                                                              r :: uu____7514
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7511
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7500
                                                            uu____7510
                                                           in
                                                        uu____7495
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7547 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7547
                                                      then
                                                        let uu____7558 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7565 =
                                                          let uu____7574 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7574]  in
                                                        uu____7558 ::
                                                          uu____7565
                                                      else []  in
                                                    let k =
                                                      let uu____7610 =
                                                        let uu____7619 =
                                                          let uu____7628 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7635 =
                                                            let uu____7644 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7644]  in
                                                          uu____7628 ::
                                                            uu____7635
                                                           in
                                                        let uu____7669 =
                                                          let uu____7678 =
                                                            let uu____7687 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7694 =
                                                              let uu____7703
                                                                =
                                                                let uu____7710
                                                                  =
                                                                  let uu____7711
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7711
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7710
                                                                 in
                                                              let uu____7712
                                                                =
                                                                let uu____7721
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7728
                                                                  =
                                                                  let uu____7737
                                                                    =
                                                                    let uu____7744
                                                                    =
                                                                    let uu____7745
                                                                    =
                                                                    let uu____7754
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7754]
                                                                     in
                                                                    let uu____7773
                                                                    =
                                                                    let uu____7776
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7776
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7745
                                                                    uu____7773
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7744
                                                                     in
                                                                  [uu____7737]
                                                                   in
                                                                uu____7721 ::
                                                                  uu____7728
                                                                 in
                                                              uu____7703 ::
                                                                uu____7712
                                                               in
                                                            uu____7687 ::
                                                              uu____7694
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7678
                                                           in
                                                        FStar_List.append
                                                          uu____7619
                                                          uu____7669
                                                         in
                                                      let uu____7821 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7610 uu____7821
                                                       in
                                                    let uu____7824 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7824 with
                                                     | (k1,uu____7832,uu____7833)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___802_7843
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.use_eq_strict
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.use_eq_strict);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___802_7843.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7845  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7845)
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
                                              (let uu____7872 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7886 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7886 with
                                                    | (usubst,uvs) ->
                                                        let uu____7909 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7910 =
                                                          let uu___815_7911 =
                                                            act  in
                                                          let uu____7912 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7913 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___815_7911.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___815_7911.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___815_7911.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7912;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7913
                                                          }  in
                                                        (uu____7909,
                                                          uu____7910))
                                                  in
                                               match uu____7872 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7917 =
                                                       let uu____7918 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7918.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7917 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7944 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7944
                                                         then
                                                           let uu____7947 =
                                                             let uu____7950 =
                                                               let uu____7951
                                                                 =
                                                                 let uu____7952
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7952
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7951
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7950
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7947
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7975 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7976 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7976 with
                                                    | (act_typ1,uu____7984,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___832_7987 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.use_eq_strict
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.use_eq_strict);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___832_7987.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7990 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7990
                                                          then
                                                            let uu____7994 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7996 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7998 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7994
                                                              uu____7996
                                                              uu____7998
                                                          else ());
                                                         (let uu____8003 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____8003
                                                          with
                                                          | (act_defn,uu____8011,g_a)
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
                                                              let uu____8015
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
                                                                    let uu____8051
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8051
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8063)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8070
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8070
                                                                     in
                                                                    let uu____8073
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8073
                                                                    with
                                                                    | 
                                                                    (k1,uu____8087,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8091
                                                                    ->
                                                                    let uu____8092
                                                                    =
                                                                    let uu____8098
                                                                    =
                                                                    let uu____8100
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8102
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8100
                                                                    uu____8102
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8098)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8092
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8015
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
                                                                    let uu____8120
                                                                    =
                                                                    let uu____8121
                                                                    =
                                                                    let uu____8122
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8122
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8121
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8120);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8124
                                                                    =
                                                                    let uu____8125
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8125.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8124
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8150
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8150
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8157
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8157
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8177
                                                                    =
                                                                    let uu____8178
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8178]
                                                                     in
                                                                    let uu____8179
                                                                    =
                                                                    let uu____8190
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8190]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8177;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8179;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8215
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8215))
                                                                    | 
                                                                    uu____8218
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8220
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8242
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8242))
                                                                     in
                                                                    match uu____8220
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
                                                                    let uu___882_8261
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___882_8261.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___882_8261.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___882_8261.FStar_Syntax_Syntax.action_params);
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
                                match uu____6699 with
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
                                      let uu____8304 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8304 ts1
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
                                          uu____8316 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8317 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8318 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___902_8321 = ed2  in
                                      let uu____8322 = cl signature  in
                                      let uu____8323 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___905_8331 = a  in
                                             let uu____8332 =
                                               let uu____8333 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8333
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8358 =
                                               let uu____8359 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8359
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___905_8331.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___905_8331.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___905_8331.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___905_8331.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8332;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8358
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___902_8321.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___902_8321.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___902_8321.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___902_8321.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8322;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8323;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___902_8321.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8385 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8385
                                      then
                                        let uu____8390 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8390
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
        let uu____8416 =
          let uu____8431 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8431 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8416 env ed quals
  
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
        let fail1 uu____8481 =
          let uu____8482 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8488 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8482 uu____8488  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8532)::(wp,uu____8534)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8563 -> fail1 ())
        | uu____8564 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8577 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8577
       then
         let uu____8582 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8582
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8599 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8599.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____8611 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8615 =
                let uu____8616 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8616 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8615
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8625 =
                   let uu____8626 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8626 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8625
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8634 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8634))
           in
        if uu____8611
        then
          let uu____8637 =
            let uu____8643 =
              let uu____8645 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8648 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8645 uu____8648
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8643)  in
          FStar_Errors.raise_error uu____8637 r
        else ());
       (let uu____8655 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8655 with
        | (us,lift,lift_ty) ->
            ((let uu____8669 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8669
              then
                let uu____8674 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8680 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8674 uu____8680
              else ());
             (let uu____8689 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8689 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  (check_no_subtyping_for_layered_combinator env lift_ty1
                     FStar_Pervasives_Native.None;
                   (let lift_t_shape_error s =
                      let uu____8707 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.source
                         in
                      let uu____8709 =
                        FStar_Ident.string_of_lid
                          sub1.FStar_Syntax_Syntax.target
                         in
                      let uu____8711 =
                        FStar_Syntax_Print.term_to_string lift_ty1  in
                      FStar_Util.format4
                        "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                        uu____8707 uu____8709 s uu____8711
                       in
                    let uu____8714 =
                      let uu____8721 =
                        let uu____8726 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____8726
                          (fun uu____8743  ->
                             match uu____8743 with
                             | (t,u) ->
                                 let uu____8754 =
                                   let uu____8755 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t
                                      in
                                   FStar_All.pipe_right uu____8755
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____8754, u))
                         in
                      match uu____8721 with
                      | (a,u_a) ->
                          let rest_bs =
                            let uu____8774 =
                              let uu____8775 =
                                FStar_Syntax_Subst.compress lift_ty1  in
                              uu____8775.FStar_Syntax_Syntax.n  in
                            match uu____8774 with
                            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____8787)
                                when
                                (FStar_List.length bs) >= (Prims.of_int (2))
                                ->
                                let uu____8815 =
                                  FStar_Syntax_Subst.open_binders bs  in
                                (match uu____8815 with
                                 | (a',uu____8825)::bs1 ->
                                     let uu____8845 =
                                       let uu____8846 =
                                         FStar_All.pipe_right bs1
                                           (FStar_List.splitAt
                                              ((FStar_List.length bs1) -
                                                 Prims.int_one))
                                          in
                                       FStar_All.pipe_right uu____8846
                                         FStar_Pervasives_Native.fst
                                        in
                                     let uu____8912 =
                                       let uu____8925 =
                                         let uu____8928 =
                                           let uu____8929 =
                                             let uu____8936 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 (FStar_Pervasives_Native.fst
                                                    a)
                                                in
                                             (a', uu____8936)  in
                                           FStar_Syntax_Syntax.NT uu____8929
                                            in
                                         [uu____8928]  in
                                       FStar_Syntax_Subst.subst_binders
                                         uu____8925
                                        in
                                     FStar_All.pipe_right uu____8845
                                       uu____8912)
                            | uu____8951 ->
                                let uu____8952 =
                                  let uu____8958 =
                                    lift_t_shape_error
                                      "either not an arrow, or not enough binders"
                                     in
                                  (FStar_Errors.Fatal_UnexpectedExpressionType,
                                    uu____8958)
                                   in
                                FStar_Errors.raise_error uu____8952 r
                             in
                          let uu____8970 =
                            let uu____8981 =
                              let uu____8986 =
                                FStar_TypeChecker_Env.push_binders env (a ::
                                  rest_bs)
                                 in
                              let uu____8993 =
                                let uu____8994 =
                                  FStar_All.pipe_right a
                                    FStar_Pervasives_Native.fst
                                   in
                                FStar_All.pipe_right uu____8994
                                  FStar_Syntax_Syntax.bv_to_name
                                 in
                              FStar_TypeChecker_Util.fresh_effect_repr_en
                                uu____8986 r sub1.FStar_Syntax_Syntax.source
                                u_a uu____8993
                               in
                            match uu____8981 with
                            | (f_sort,g) ->
                                let uu____9015 =
                                  let uu____9022 =
                                    FStar_Syntax_Syntax.gen_bv "f"
                                      FStar_Pervasives_Native.None f_sort
                                     in
                                  FStar_All.pipe_right uu____9022
                                    FStar_Syntax_Syntax.mk_binder
                                   in
                                (uu____9015, g)
                             in
                          (match uu____8970 with
                           | (f_b,g_f_b) ->
                               let bs = a ::
                                 (FStar_List.append rest_bs [f_b])  in
                               let uu____9089 =
                                 let uu____9094 =
                                   FStar_TypeChecker_Env.push_binders env bs
                                    in
                                 let uu____9095 =
                                   let uu____9096 =
                                     FStar_All.pipe_right a
                                       FStar_Pervasives_Native.fst
                                      in
                                   FStar_All.pipe_right uu____9096
                                     FStar_Syntax_Syntax.bv_to_name
                                    in
                                 FStar_TypeChecker_Util.fresh_effect_repr_en
                                   uu____9094 r
                                   sub1.FStar_Syntax_Syntax.target u_a
                                   uu____9095
                                  in
                               (match uu____9089 with
                                | (repr,g_repr) ->
                                    let uu____9113 =
                                      let uu____9118 =
                                        FStar_TypeChecker_Env.push_binders
                                          env bs
                                         in
                                      let uu____9119 =
                                        let uu____9121 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.source
                                           in
                                        let uu____9123 =
                                          FStar_Ident.string_of_lid
                                            sub1.FStar_Syntax_Syntax.target
                                           in
                                        FStar_Util.format2
                                          "implicit for pure_wp in typechecking lift %s~>%s"
                                          uu____9121 uu____9123
                                         in
                                      pure_wp_uvar uu____9118 repr uu____9119
                                        r
                                       in
                                    (match uu____9113 with
                                     | (pure_wp_uvar1,guard_wp) ->
                                         let c =
                                           let uu____9135 =
                                             let uu____9136 =
                                               let uu____9137 =
                                                 FStar_TypeChecker_Env.new_u_univ
                                                   ()
                                                  in
                                               [uu____9137]  in
                                             let uu____9138 =
                                               let uu____9149 =
                                                 FStar_All.pipe_right
                                                   pure_wp_uvar1
                                                   FStar_Syntax_Syntax.as_arg
                                                  in
                                               [uu____9149]  in
                                             {
                                               FStar_Syntax_Syntax.comp_univs
                                                 = uu____9136;
                                               FStar_Syntax_Syntax.effect_name
                                                 =
                                                 FStar_Parser_Const.effect_PURE_lid;
                                               FStar_Syntax_Syntax.result_typ
                                                 = repr;
                                               FStar_Syntax_Syntax.effect_args
                                                 = uu____9138;
                                               FStar_Syntax_Syntax.flags = []
                                             }  in
                                           FStar_Syntax_Syntax.mk_Comp
                                             uu____9135
                                            in
                                         let uu____9182 =
                                           FStar_Syntax_Util.arrow bs c  in
                                         let uu____9185 =
                                           let uu____9186 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_f_b g_repr
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             uu____9186 guard_wp
                                            in
                                         (uu____9182, uu____9185))))
                       in
                    match uu____8714 with
                    | (k,g_k) ->
                        ((let uu____9196 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9196
                          then
                            let uu____9201 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1
                              "tc_layered_lift: before unification k: %s\n"
                              uu____9201
                          else ());
                         (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k
                             in
                          FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                          FStar_TypeChecker_Rel.force_trivial_guard env g;
                          (let uu____9210 =
                             FStar_All.pipe_left
                               (FStar_TypeChecker_Env.debug env0)
                               (FStar_Options.Other "LayeredEffects")
                              in
                           if uu____9210
                           then
                             let uu____9215 =
                               FStar_Syntax_Print.term_to_string k  in
                             FStar_Util.print1 "After unification k: %s\n"
                               uu____9215
                           else ());
                          (let sub2 =
                             let uu___998_9221 = sub1  in
                             let uu____9222 =
                               let uu____9225 =
                                 let uu____9226 =
                                   let uu____9229 =
                                     FStar_All.pipe_right k
                                       (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                          env)
                                      in
                                   FStar_All.pipe_right uu____9229
                                     (FStar_Syntax_Subst.close_univ_vars us1)
                                    in
                                 (us1, uu____9226)  in
                               FStar_Pervasives_Native.Some uu____9225  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___998_9221.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___998_9221.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9222;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9241 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9241
                            then
                              let uu____9246 =
                                FStar_Syntax_Print.sub_eff_to_string sub2  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9246
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
          let uu____9283 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9283  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9286 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9286
        then tc_layered_lift env sub1
        else
          (let uu____9293 =
             let uu____9300 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9300
              in
           match uu____9293 with
           | (a,wp_a_src) ->
               let uu____9307 =
                 let uu____9314 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9314
                  in
               (match uu____9307 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9322 =
                        let uu____9325 =
                          let uu____9326 =
                            let uu____9333 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9333)  in
                          FStar_Syntax_Syntax.NT uu____9326  in
                        [uu____9325]  in
                      FStar_Syntax_Subst.subst uu____9322 wp_b_tgt  in
                    let expected_k =
                      let uu____9341 =
                        let uu____9350 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9357 =
                          let uu____9366 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9366]  in
                        uu____9350 :: uu____9357  in
                      let uu____9391 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9341 uu____9391  in
                    let repr_type eff_name a1 wp =
                      (let uu____9413 =
                         let uu____9415 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9415  in
                       if uu____9413
                       then
                         let uu____9418 =
                           let uu____9424 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9424)
                            in
                         let uu____9428 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9418 uu____9428
                       else ());
                      (let uu____9431 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9431 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9464 =
                               let uu____9465 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9465
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9464
                              in
                           let uu____9472 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9473 =
                             let uu____9480 =
                               let uu____9481 =
                                 let uu____9498 =
                                   let uu____9509 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9518 =
                                     let uu____9529 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9529]  in
                                   uu____9509 :: uu____9518  in
                                 (repr, uu____9498)  in
                               FStar_Syntax_Syntax.Tm_app uu____9481  in
                             FStar_Syntax_Syntax.mk uu____9480  in
                           uu____9473 FStar_Pervasives_Native.None uu____9472)
                       in
                    let uu____9574 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9747 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9758 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9758 with
                              | (usubst,uvs1) ->
                                  let uu____9781 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9782 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9781, uu____9782)
                            else (env, lift_wp)  in
                          (match uu____9747 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9832 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9832))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9903 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9918 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9918 with
                              | (usubst,uvs) ->
                                  let uu____9943 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9943)
                            else ([], lift)  in
                          (match uu____9903 with
                           | (uvs,lift1) ->
                               ((let uu____9979 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9979
                                 then
                                   let uu____9983 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9983
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9989 =
                                   let uu____9996 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9996 lift1
                                    in
                                 match uu____9989 with
                                 | (lift2,comp,uu____10021) ->
                                     let uu____10022 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10022 with
                                      | (uu____10051,lift_wp,lift_elab) ->
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
                                            let uu____10083 =
                                              let uu____10094 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10094
                                               in
                                            let uu____10111 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10083, uu____10111)
                                          else
                                            (let uu____10140 =
                                               let uu____10151 =
                                                 let uu____10160 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10160)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10151
                                                in
                                             let uu____10175 =
                                               let uu____10184 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10184)  in
                                             (uu____10140, uu____10175))))))
                       in
                    (match uu____9574 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1082_10248 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1082_10248.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1082_10248.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1082_10248.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1082_10248.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1082_10248.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1082_10248.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1082_10248.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1082_10248.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1082_10248.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1082_10248.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1082_10248.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1082_10248.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1082_10248.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1082_10248.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1082_10248.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1082_10248.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1082_10248.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.use_eq_strict =
                               (uu___1082_10248.FStar_TypeChecker_Env.use_eq_strict);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1082_10248.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1082_10248.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1082_10248.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1082_10248.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1082_10248.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1082_10248.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1082_10248.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1082_10248.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1082_10248.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1082_10248.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1082_10248.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1082_10248.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1082_10248.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1082_10248.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1082_10248.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1082_10248.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1082_10248.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1082_10248.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1082_10248.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1082_10248.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1082_10248.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1082_10248.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1082_10248.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1082_10248.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1082_10248.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1082_10248.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1082_10248.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10281 =
                                 let uu____10286 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10286 with
                                 | (usubst,uvs1) ->
                                     let uu____10309 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10310 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10309, uu____10310)
                                  in
                               (match uu____10281 with
                                | (env2,lift2) ->
                                    let uu____10315 =
                                      let uu____10322 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10322
                                       in
                                    (match uu____10315 with
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
                                             let uu____10348 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10349 =
                                               let uu____10356 =
                                                 let uu____10357 =
                                                   let uu____10374 =
                                                     let uu____10385 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10394 =
                                                       let uu____10405 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10405]  in
                                                     uu____10385 ::
                                                       uu____10394
                                                      in
                                                   (lift_wp1, uu____10374)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10357
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10356
                                                in
                                             uu____10349
                                               FStar_Pervasives_Native.None
                                               uu____10348
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10453 =
                                             let uu____10462 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10469 =
                                               let uu____10478 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10485 =
                                                 let uu____10494 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10494]  in
                                               uu____10478 :: uu____10485  in
                                             uu____10462 :: uu____10469  in
                                           let uu____10525 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10453 uu____10525
                                            in
                                         let uu____10528 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10528 with
                                          | (expected_k2,uu____10538,uu____10539)
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
                                                   let uu____10547 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10547))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10555 =
                             let uu____10557 =
                               let uu____10559 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10559
                                 FStar_List.length
                                in
                             uu____10557 <> Prims.int_one  in
                           if uu____10555
                           then
                             let uu____10582 =
                               let uu____10588 =
                                 let uu____10590 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10592 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10594 =
                                   let uu____10596 =
                                     let uu____10598 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10598
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10596
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10590 uu____10592 uu____10594
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10588)
                                in
                             FStar_Errors.raise_error uu____10582 r
                           else ());
                          (let uu____10625 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10628 =
                                  let uu____10630 =
                                    let uu____10633 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10633
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10630
                                    FStar_List.length
                                   in
                                uu____10628 <> Prims.int_one)
                              in
                           if uu____10625
                           then
                             let uu____10672 =
                               let uu____10678 =
                                 let uu____10680 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10682 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10684 =
                                   let uu____10686 =
                                     let uu____10688 =
                                       let uu____10691 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10691
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10688
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10686
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10680 uu____10682 uu____10684
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10678)
                                in
                             FStar_Errors.raise_error uu____10672 r
                           else ());
                          (let uu___1119_10733 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1119_10733.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1119_10733.FStar_Syntax_Syntax.target);
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
    fun uu____10764  ->
      fun r  ->
        match uu____10764 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10787 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10815 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10815 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10846 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10846 c  in
                     let uu____10855 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10855, uvs1, tps1, c1))
               in
            (match uu____10787 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10875 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10875 with
                  | (tps2,c2) ->
                      let uu____10890 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10890 with
                       | (tps3,env3,us) ->
                           let uu____10908 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10908 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10934)::uu____10935 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10954 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10962 =
                                    let uu____10964 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10964  in
                                  if uu____10962
                                  then
                                    let uu____10967 =
                                      let uu____10973 =
                                        let uu____10975 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10977 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10975 uu____10977
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10973)
                                       in
                                    FStar_Errors.raise_error uu____10967 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____10985 =
                                    let uu____10986 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10986
                                     in
                                  match uu____10985 with
                                  | (uvs2,t) ->
                                      let uu____11015 =
                                        let uu____11020 =
                                          let uu____11033 =
                                            let uu____11034 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11034.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11033)  in
                                        match uu____11020 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11049,c5)) -> ([], c5)
                                        | (uu____11091,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11130 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11015 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11162 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11162 with
                                               | (uu____11167,t1) ->
                                                   let uu____11169 =
                                                     let uu____11175 =
                                                       let uu____11177 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11179 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11183 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11177
                                                         uu____11179
                                                         uu____11183
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11175)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11169 r)
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
              let uu____11225 = FStar_Ident.string_of_lid m  in
              let uu____11227 = FStar_Ident.string_of_lid n1  in
              let uu____11229 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11225 uu____11227
                uu____11229
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            (let uu____11238 =
               FStar_TypeChecker_Env.is_user_reifiable_effect env p  in
             if uu____11238
             then
               let uu____11241 =
                 let uu____11247 =
                   let uu____11249 = FStar_Ident.string_of_lid p  in
                   FStar_Util.format2
                     "Error typechecking the polymonadic bind %s, the final effect %s is reifiable and reification of polymondic binds is not yet implemented"
                     eff_name uu____11249
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____11247)  in
               FStar_Errors.raise_error uu____11241 r
             else ());
            (let uu____11255 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts
                in
             match uu____11255 with
             | (us,t,ty) ->
                 let uu____11271 = FStar_Syntax_Subst.open_univ_vars us ty
                    in
                 (match uu____11271 with
                  | (us1,ty1) ->
                      let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                         in
                      (check_no_subtyping_for_layered_combinator env1 ty1
                         FStar_Pervasives_Native.None;
                       (let uu____11284 =
                          let uu____11289 = FStar_Syntax_Util.type_u ()  in
                          FStar_All.pipe_right uu____11289
                            (fun uu____11306  ->
                               match uu____11306 with
                               | (t1,u) ->
                                   let uu____11317 =
                                     let uu____11318 =
                                       FStar_Syntax_Syntax.gen_bv "a"
                                         FStar_Pervasives_Native.None t1
                                        in
                                     FStar_All.pipe_right uu____11318
                                       FStar_Syntax_Syntax.mk_binder
                                      in
                                   (uu____11317, u))
                           in
                        match uu____11284 with
                        | (a,u_a) ->
                            let uu____11326 =
                              let uu____11331 = FStar_Syntax_Util.type_u ()
                                 in
                              FStar_All.pipe_right uu____11331
                                (fun uu____11348  ->
                                   match uu____11348 with
                                   | (t1,u) ->
                                       let uu____11359 =
                                         let uu____11360 =
                                           FStar_Syntax_Syntax.gen_bv "b"
                                             FStar_Pervasives_Native.None t1
                                            in
                                         FStar_All.pipe_right uu____11360
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____11359, u))
                               in
                            (match uu____11326 with
                             | (b,u_b) ->
                                 let rest_bs =
                                   let uu____11377 =
                                     let uu____11378 =
                                       FStar_Syntax_Subst.compress ty1  in
                                     uu____11378.FStar_Syntax_Syntax.n  in
                                   match uu____11377 with
                                   | FStar_Syntax_Syntax.Tm_arrow
                                       (bs,uu____11390) when
                                       (FStar_List.length bs) >=
                                         (Prims.of_int (4))
                                       ->
                                       let uu____11418 =
                                         FStar_Syntax_Subst.open_binders bs
                                          in
                                       (match uu____11418 with
                                        | (a',uu____11428)::(b',uu____11430)::bs1
                                            ->
                                            let uu____11460 =
                                              let uu____11461 =
                                                FStar_All.pipe_right bs1
                                                  (FStar_List.splitAt
                                                     ((FStar_List.length bs1)
                                                        - (Prims.of_int (2))))
                                                 in
                                              FStar_All.pipe_right
                                                uu____11461
                                                FStar_Pervasives_Native.fst
                                               in
                                            let uu____11559 =
                                              let uu____11572 =
                                                let uu____11575 =
                                                  let uu____11576 =
                                                    let uu____11583 =
                                                      let uu____11586 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____11586
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    (a', uu____11583)  in
                                                  FStar_Syntax_Syntax.NT
                                                    uu____11576
                                                   in
                                                let uu____11599 =
                                                  let uu____11602 =
                                                    let uu____11603 =
                                                      let uu____11610 =
                                                        let uu____11613 =
                                                          FStar_All.pipe_right
                                                            b
                                                            FStar_Pervasives_Native.fst
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____11613
                                                          FStar_Syntax_Syntax.bv_to_name
                                                         in
                                                      (b', uu____11610)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____11603
                                                     in
                                                  [uu____11602]  in
                                                uu____11575 :: uu____11599
                                                 in
                                              FStar_Syntax_Subst.subst_binders
                                                uu____11572
                                               in
                                            FStar_All.pipe_right uu____11460
                                              uu____11559)
                                   | uu____11634 ->
                                       let uu____11635 =
                                         let uu____11641 =
                                           let uu____11643 =
                                             FStar_Syntax_Print.tag_of_term
                                               ty1
                                              in
                                           let uu____11645 =
                                             FStar_Syntax_Print.term_to_string
                                               ty1
                                              in
                                           FStar_Util.format3
                                             "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                             eff_name uu____11643 uu____11645
                                            in
                                         (FStar_Errors.Fatal_UnexpectedEffect,
                                           uu____11641)
                                          in
                                       FStar_Errors.raise_error uu____11635 r
                                    in
                                 let bs = a :: b :: rest_bs  in
                                 let uu____11678 =
                                   let uu____11689 =
                                     let uu____11694 =
                                       FStar_TypeChecker_Env.push_binders
                                         env1 bs
                                        in
                                     let uu____11695 =
                                       let uu____11696 =
                                         FStar_All.pipe_right a
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_All.pipe_right uu____11696
                                         FStar_Syntax_Syntax.bv_to_name
                                        in
                                     FStar_TypeChecker_Util.fresh_effect_repr_en
                                       uu____11694 r m u_a uu____11695
                                      in
                                   match uu____11689 with
                                   | (repr,g) ->
                                       let uu____11717 =
                                         let uu____11724 =
                                           FStar_Syntax_Syntax.gen_bv "f"
                                             FStar_Pervasives_Native.None
                                             repr
                                            in
                                         FStar_All.pipe_right uu____11724
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       (uu____11717, g)
                                    in
                                 (match uu____11678 with
                                  | (f,guard_f) ->
                                      let uu____11756 =
                                        let x_a =
                                          let uu____11774 =
                                            let uu____11775 =
                                              let uu____11776 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11776
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_Syntax_Syntax.gen_bv "x"
                                              FStar_Pervasives_Native.None
                                              uu____11775
                                             in
                                          FStar_All.pipe_right uu____11774
                                            FStar_Syntax_Syntax.mk_binder
                                           in
                                        let uu____11792 =
                                          let uu____11797 =
                                            FStar_TypeChecker_Env.push_binders
                                              env1
                                              (FStar_List.append bs [x_a])
                                             in
                                          let uu____11816 =
                                            let uu____11817 =
                                              FStar_All.pipe_right b
                                                FStar_Pervasives_Native.fst
                                               in
                                            FStar_All.pipe_right uu____11817
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          FStar_TypeChecker_Util.fresh_effect_repr_en
                                            uu____11797 r n1 u_b uu____11816
                                           in
                                        match uu____11792 with
                                        | (repr,g) ->
                                            let uu____11838 =
                                              let uu____11845 =
                                                let uu____11846 =
                                                  let uu____11847 =
                                                    let uu____11850 =
                                                      let uu____11853 =
                                                        FStar_TypeChecker_Env.new_u_univ
                                                          ()
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____11853
                                                       in
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      repr uu____11850
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    [x_a] uu____11847
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "g"
                                                  FStar_Pervasives_Native.None
                                                  uu____11846
                                                 in
                                              FStar_All.pipe_right
                                                uu____11845
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____11838, g)
                                         in
                                      (match uu____11756 with
                                       | (g,guard_g) ->
                                           let uu____11897 =
                                             let uu____11902 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs
                                                in
                                             let uu____11903 =
                                               let uu____11904 =
                                                 FStar_All.pipe_right b
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               FStar_All.pipe_right
                                                 uu____11904
                                                 FStar_Syntax_Syntax.bv_to_name
                                                in
                                             FStar_TypeChecker_Util.fresh_effect_repr_en
                                               uu____11902 r p u_b
                                               uu____11903
                                              in
                                           (match uu____11897 with
                                            | (repr,guard_repr) ->
                                                let k =
                                                  let uu____11922 =
                                                    FStar_Syntax_Syntax.mk_Total'
                                                      repr
                                                      (FStar_Pervasives_Native.Some
                                                         u_b)
                                                     in
                                                  FStar_Syntax_Util.arrow
                                                    (FStar_List.append bs
                                                       [f; g]) uu____11922
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
                                                   guard_eq];
                                                 (let uu____11952 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env1)
                                                      FStar_Options.Extreme
                                                     in
                                                  if uu____11952
                                                  then
                                                    let uu____11956 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        (us1, t)
                                                       in
                                                    let uu____11962 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        (us1, k)
                                                       in
                                                    FStar_Util.print3
                                                      "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                      eff_name uu____11956
                                                      uu____11962
                                                  else ());
                                                 (let uu____11972 =
                                                    let uu____11978 =
                                                      FStar_Util.format1
                                                        "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                        eff_name
                                                       in
                                                    (FStar_Errors.Warning_BleedingEdge_Feature,
                                                      uu____11978)
                                                     in
                                                  FStar_Errors.log_issue r
                                                    uu____11972);
                                                 (let uu____11982 =
                                                    let uu____11983 =
                                                      let uu____11986 =
                                                        FStar_All.pipe_right
                                                          k
                                                          (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                             env1)
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____11986
                                                        (FStar_Syntax_Subst.close_univ_vars
                                                           us1)
                                                       in
                                                    (us1, uu____11983)  in
                                                  ((us1, t), uu____11982)))))))))))
  