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
                    FStar_TypeChecker_Env.use_eq = true;
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
                    FStar_TypeChecker_Env.use_eq = true;
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
                           let uu____1353 = fresh_a_and_u_a "a"  in
                           (match uu____1353 with
                            | (a,u_a) ->
                                let x_a = fresh_x_a "x" a  in
                                let rest_bs =
                                  let uu____1384 =
                                    let uu____1385 =
                                      FStar_Syntax_Subst.compress ty  in
                                    uu____1385.FStar_Syntax_Syntax.n  in
                                  match uu____1384 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____1397) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (2))
                                      ->
                                      let uu____1425 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____1425 with
                                       | (a',uu____1435)::(x',uu____1437)::bs1
                                           ->
                                           let uu____1467 =
                                             let uu____1468 =
                                               let uu____1473 =
                                                 let uu____1476 =
                                                   let uu____1477 =
                                                     let uu____1484 =
                                                       FStar_Syntax_Syntax.bv_to_name
                                                         (FStar_Pervasives_Native.fst
                                                            a)
                                                        in
                                                     (a', uu____1484)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____1477
                                                    in
                                                 [uu____1476]  in
                                               FStar_Syntax_Subst.subst_binders
                                                 uu____1473
                                                in
                                             FStar_All.pipe_right bs1
                                               uu____1468
                                              in
                                           let uu____1491 =
                                             let uu____1504 =
                                               let uu____1507 =
                                                 let uu____1508 =
                                                   let uu____1515 =
                                                     FStar_Syntax_Syntax.bv_to_name
                                                       (FStar_Pervasives_Native.fst
                                                          x_a)
                                                      in
                                                   (x', uu____1515)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____1508
                                                  in
                                               [uu____1507]  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____1504
                                              in
                                           FStar_All.pipe_right uu____1467
                                             uu____1491)
                                  | uu____1530 ->
                                      not_an_arrow_error "return"
                                        (Prims.of_int (2)) ty r
                                   in
                                let bs = a :: x_a :: rest_bs  in
                                let uu____1554 =
                                  let uu____1559 =
                                    FStar_TypeChecker_Env.push_binders env bs
                                     in
                                  let uu____1560 =
                                    FStar_All.pipe_right
                                      (FStar_Pervasives_Native.fst a)
                                      FStar_Syntax_Syntax.bv_to_name
                                     in
                                  fresh_repr r uu____1559 u_a uu____1560  in
                                (match uu____1554 with
                                 | (repr1,g) ->
                                     let k =
                                       let uu____1580 =
                                         FStar_Syntax_Syntax.mk_Total' repr1
                                           (FStar_Pervasives_Native.Some u_a)
                                          in
                                       FStar_Syntax_Util.arrow bs uu____1580
                                        in
                                     let g_eq =
                                       FStar_TypeChecker_Rel.teq env ty k  in
                                     ((let uu____1585 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           g_eq
                                          in
                                       FStar_TypeChecker_Rel.force_trivial_guard
                                         env uu____1585);
                                      (let k1 =
                                         FStar_All.pipe_right k
                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                              env)
                                          in
                                       check_no_subtyping_for_layered_combinator
                                         env k1 FStar_Pervasives_Native.None;
                                       (let uu____1588 =
                                          FStar_Syntax_Subst.close_univ_vars
                                            us k1
                                           in
                                        (ret_us, ret_t, uu____1588)))))))
                   in
                log_combinator "return_repr" return_repr;
                (let bind_repr =
                   let bind_repr_ts =
                     let uu____1617 =
                       FStar_All.pipe_right ed
                         FStar_Syntax_Util.get_bind_repr
                        in
                     FStar_All.pipe_right uu____1617 FStar_Util.must  in
                   let r =
                     (FStar_Pervasives_Native.snd bind_repr_ts).FStar_Syntax_Syntax.pos
                      in
                   let uu____1645 =
                     check_and_gen1 "bind_repr" (Prims.of_int (2))
                       bind_repr_ts
                      in
                   match uu____1645 with
                   | (bind_us,bind_t,bind_ty) ->
                       let uu____1669 =
                         FStar_Syntax_Subst.open_univ_vars bind_us bind_ty
                          in
                       (match uu____1669 with
                        | (us,ty) ->
                            let env =
                              FStar_TypeChecker_Env.push_univ_vars env0 us
                               in
                            let uu____1689 = fresh_a_and_u_a "a"  in
                            (match uu____1689 with
                             | (a,u_a) ->
                                 let uu____1709 = fresh_a_and_u_a "b"  in
                                 (match uu____1709 with
                                  | (b,u_b) ->
                                      let rest_bs =
                                        let uu____1738 =
                                          let uu____1739 =
                                            FStar_Syntax_Subst.compress ty
                                             in
                                          uu____1739.FStar_Syntax_Syntax.n
                                           in
                                        match uu____1738 with
                                        | FStar_Syntax_Syntax.Tm_arrow
                                            (bs,uu____1751) when
                                            (FStar_List.length bs) >=
                                              (Prims.of_int (4))
                                            ->
                                            let uu____1779 =
                                              FStar_Syntax_Subst.open_binders
                                                bs
                                               in
                                            (match uu____1779 with
                                             | (a',uu____1789)::(b',uu____1791)::bs1
                                                 ->
                                                 let uu____1821 =
                                                   let uu____1822 =
                                                     FStar_All.pipe_right bs1
                                                       (FStar_List.splitAt
                                                          ((FStar_List.length
                                                              bs1)
                                                             -
                                                             (Prims.of_int (2))))
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____1822
                                                     FStar_Pervasives_Native.fst
                                                    in
                                                 let uu____1888 =
                                                   let uu____1901 =
                                                     let uu____1904 =
                                                       let uu____1905 =
                                                         let uu____1912 =
                                                           FStar_Syntax_Syntax.bv_to_name
                                                             (FStar_Pervasives_Native.fst
                                                                a)
                                                            in
                                                         (a', uu____1912)  in
                                                       FStar_Syntax_Syntax.NT
                                                         uu____1905
                                                        in
                                                     let uu____1919 =
                                                       let uu____1922 =
                                                         let uu____1923 =
                                                           let uu____1930 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               (FStar_Pervasives_Native.fst
                                                                  b)
                                                              in
                                                           (b', uu____1930)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____1923
                                                          in
                                                       [uu____1922]  in
                                                     uu____1904 :: uu____1919
                                                      in
                                                   FStar_Syntax_Subst.subst_binders
                                                     uu____1901
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____1821 uu____1888)
                                        | uu____1945 ->
                                            not_an_arrow_error "bind"
                                              (Prims.of_int (4)) ty r
                                         in
                                      let bs = a :: b :: rest_bs  in
                                      let uu____1969 =
                                        let uu____1980 =
                                          let uu____1985 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____1986 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____1985 u_a
                                            uu____1986
                                           in
                                        match uu____1980 with
                                        | (repr1,g) ->
                                            let uu____2001 =
                                              let uu____2008 =
                                                FStar_Syntax_Syntax.gen_bv
                                                  "f"
                                                  FStar_Pervasives_Native.None
                                                  repr1
                                                 in
                                              FStar_All.pipe_right uu____2008
                                                FStar_Syntax_Syntax.mk_binder
                                               in
                                            (uu____2001, g)
                                         in
                                      (match uu____1969 with
                                       | (f,guard_f) ->
                                           let uu____2048 =
                                             let x_a = fresh_x_a "x" a  in
                                             let uu____2061 =
                                               let uu____2066 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env
                                                   (FStar_List.append bs
                                                      [x_a])
                                                  in
                                               let uu____2085 =
                                                 FStar_All.pipe_right
                                                   (FStar_Pervasives_Native.fst
                                                      b)
                                                   FStar_Syntax_Syntax.bv_to_name
                                                  in
                                               fresh_repr r uu____2066 u_b
                                                 uu____2085
                                                in
                                             match uu____2061 with
                                             | (repr1,g) ->
                                                 let uu____2100 =
                                                   let uu____2107 =
                                                     let uu____2108 =
                                                       let uu____2109 =
                                                         let uu____2112 =
                                                           let uu____2115 =
                                                             FStar_TypeChecker_Env.new_u_univ
                                                               ()
                                                              in
                                                           FStar_Pervasives_Native.Some
                                                             uu____2115
                                                            in
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1 uu____2112
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         [x_a] uu____2109
                                                        in
                                                     FStar_Syntax_Syntax.gen_bv
                                                       "g"
                                                       FStar_Pervasives_Native.None
                                                       uu____2108
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____2107
                                                     FStar_Syntax_Syntax.mk_binder
                                                    in
                                                 (uu____2100, g)
                                              in
                                           (match uu____2048 with
                                            | (g,guard_g) ->
                                                let uu____2167 =
                                                  let uu____2172 =
                                                    FStar_TypeChecker_Env.push_binders
                                                      env bs
                                                     in
                                                  let uu____2173 =
                                                    FStar_All.pipe_right
                                                      (FStar_Pervasives_Native.fst
                                                         b)
                                                      FStar_Syntax_Syntax.bv_to_name
                                                     in
                                                  fresh_repr r uu____2172 u_b
                                                    uu____2173
                                                   in
                                                (match uu____2167 with
                                                 | (repr1,guard_repr) ->
                                                     let k =
                                                       let uu____2193 =
                                                         FStar_Syntax_Syntax.mk_Total'
                                                           repr1
                                                           (FStar_Pervasives_Native.Some
                                                              u_b)
                                                          in
                                                       FStar_Syntax_Util.arrow
                                                         (FStar_List.append
                                                            bs [f; g])
                                                         uu____2193
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
                                                      (let k1 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env)
                                                          in
                                                       check_no_subtyping_for_layered_combinator
                                                         env k1
                                                         FStar_Pervasives_Native.None;
                                                       (let uu____2224 =
                                                          FStar_Syntax_Subst.close_univ_vars
                                                            bind_us k1
                                                           in
                                                        (bind_us, bind_t,
                                                          uu____2224))))))))))
                    in
                 log_combinator "bind_repr" bind_repr;
                 (let stronger_repr =
                    let stronger_repr =
                      let uu____2253 =
                        FStar_All.pipe_right ed
                          FStar_Syntax_Util.get_stronger_repr
                         in
                      FStar_All.pipe_right uu____2253 FStar_Util.must  in
                    let r =
                      (FStar_Pervasives_Native.snd stronger_repr).FStar_Syntax_Syntax.pos
                       in
                    let uu____2265 =
                      check_and_gen1 "stronger_repr" Prims.int_one
                        stronger_repr
                       in
                    match uu____2265 with
                    | (stronger_us,stronger_t,stronger_ty) ->
                        ((let uu____2290 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____2290
                          then
                            let uu____2295 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_t)
                               in
                            let uu____2301 =
                              FStar_Syntax_Print.tscheme_to_string
                                (stronger_us, stronger_ty)
                               in
                            FStar_Util.print2
                              "stronger combinator typechecked with term: %s and type: %s\n"
                              uu____2295 uu____2301
                          else ());
                         (let uu____2310 =
                            FStar_Syntax_Subst.open_univ_vars stronger_us
                              stronger_ty
                             in
                          match uu____2310 with
                          | (us,ty) ->
                              let env =
                                FStar_TypeChecker_Env.push_univ_vars env0 us
                                 in
                              let uu____2330 = fresh_a_and_u_a "a"  in
                              (match uu____2330 with
                               | (a,u) ->
                                   let rest_bs =
                                     let uu____2359 =
                                       let uu____2360 =
                                         FStar_Syntax_Subst.compress ty  in
                                       uu____2360.FStar_Syntax_Syntax.n  in
                                     match uu____2359 with
                                     | FStar_Syntax_Syntax.Tm_arrow
                                         (bs,uu____2372) when
                                         (FStar_List.length bs) >=
                                           (Prims.of_int (2))
                                         ->
                                         let uu____2400 =
                                           FStar_Syntax_Subst.open_binders bs
                                            in
                                         (match uu____2400 with
                                          | (a',uu____2410)::bs1 ->
                                              let uu____2430 =
                                                let uu____2431 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.splitAt
                                                       ((FStar_List.length
                                                           bs1)
                                                          - Prims.int_one))
                                                   in
                                                FStar_All.pipe_right
                                                  uu____2431
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              let uu____2529 =
                                                let uu____2542 =
                                                  let uu____2545 =
                                                    let uu____2546 =
                                                      let uu____2553 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          (FStar_Pervasives_Native.fst
                                                             a)
                                                         in
                                                      (a', uu____2553)  in
                                                    FStar_Syntax_Syntax.NT
                                                      uu____2546
                                                     in
                                                  [uu____2545]  in
                                                FStar_Syntax_Subst.subst_binders
                                                  uu____2542
                                                 in
                                              FStar_All.pipe_right uu____2430
                                                uu____2529)
                                     | uu____2568 ->
                                         not_an_arrow_error "stronger"
                                           (Prims.of_int (2)) ty r
                                      in
                                   let bs = a :: rest_bs  in
                                   let uu____2586 =
                                     let uu____2597 =
                                       let uu____2602 =
                                         FStar_TypeChecker_Env.push_binders
                                           env bs
                                          in
                                       let uu____2603 =
                                         FStar_All.pipe_right
                                           (FStar_Pervasives_Native.fst a)
                                           FStar_Syntax_Syntax.bv_to_name
                                          in
                                       fresh_repr r uu____2602 u uu____2603
                                        in
                                     match uu____2597 with
                                     | (repr1,g) ->
                                         let uu____2618 =
                                           let uu____2625 =
                                             FStar_Syntax_Syntax.gen_bv "f"
                                               FStar_Pervasives_Native.None
                                               repr1
                                              in
                                           FStar_All.pipe_right uu____2625
                                             FStar_Syntax_Syntax.mk_binder
                                            in
                                         (uu____2618, g)
                                      in
                                   (match uu____2586 with
                                    | (f,guard_f) ->
                                        let uu____2665 =
                                          let uu____2670 =
                                            FStar_TypeChecker_Env.push_binders
                                              env bs
                                             in
                                          let uu____2671 =
                                            FStar_All.pipe_right
                                              (FStar_Pervasives_Native.fst a)
                                              FStar_Syntax_Syntax.bv_to_name
                                             in
                                          fresh_repr r uu____2670 u
                                            uu____2671
                                           in
                                        (match uu____2665 with
                                         | (ret_t,guard_ret_t) ->
                                             let uu____2688 =
                                               let uu____2693 =
                                                 FStar_TypeChecker_Env.push_binders
                                                   env bs
                                                  in
                                               let uu____2694 =
                                                 FStar_Util.format1
                                                   "implicit for pure_wp in checking stronger for %s"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                  in
                                               pure_wp_uvar uu____2693 ret_t
                                                 uu____2694 r
                                                in
                                             (match uu____2688 with
                                              | (pure_wp_uvar1,guard_wp) ->
                                                  let c =
                                                    let uu____2712 =
                                                      let uu____2713 =
                                                        let uu____2714 =
                                                          FStar_TypeChecker_Env.new_u_univ
                                                            ()
                                                           in
                                                        [uu____2714]  in
                                                      let uu____2715 =
                                                        let uu____2726 =
                                                          FStar_All.pipe_right
                                                            pure_wp_uvar1
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____2726]  in
                                                      {
                                                        FStar_Syntax_Syntax.comp_univs
                                                          = uu____2713;
                                                        FStar_Syntax_Syntax.effect_name
                                                          =
                                                          FStar_Parser_Const.effect_PURE_lid;
                                                        FStar_Syntax_Syntax.result_typ
                                                          = ret_t;
                                                        FStar_Syntax_Syntax.effect_args
                                                          = uu____2715;
                                                        FStar_Syntax_Syntax.flags
                                                          = []
                                                      }  in
                                                    FStar_Syntax_Syntax.mk_Comp
                                                      uu____2712
                                                     in
                                                  let k =
                                                    FStar_Syntax_Util.arrow
                                                      (FStar_List.append bs
                                                         [f]) c
                                                     in
                                                  ((let uu____2781 =
                                                      FStar_All.pipe_left
                                                        (FStar_TypeChecker_Env.debug
                                                           env)
                                                        (FStar_Options.Other
                                                           "LayeredEffects")
                                                       in
                                                    if uu____2781
                                                    then
                                                      let uu____2786 =
                                                        FStar_Syntax_Print.term_to_string
                                                          k
                                                         in
                                                      FStar_Util.print1
                                                        "Expected type before unification: %s\n"
                                                        uu____2786
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
                                                    (let k1 =
                                                       let uu____2794 =
                                                         FStar_All.pipe_right
                                                           k
                                                           (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                              env)
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____2794
                                                         (FStar_TypeChecker_Normalize.normalize
                                                            [FStar_TypeChecker_Env.Beta;
                                                            FStar_TypeChecker_Env.Eager_unfolding]
                                                            env)
                                                        in
                                                     check_no_subtyping_for_layered_combinator
                                                       env k1
                                                       FStar_Pervasives_Native.None;
                                                     (let uu____2796 =
                                                        FStar_Syntax_Subst.close_univ_vars
                                                          stronger_us k1
                                                         in
                                                      (stronger_us,
                                                        stronger_t,
                                                        uu____2796)))))))))))
                     in
                  log_combinator "stronger_repr" stronger_repr;
                  (let if_then_else1 =
                     let if_then_else_ts =
                       let uu____2825 =
                         FStar_All.pipe_right ed
                           FStar_Syntax_Util.get_layered_if_then_else_combinator
                          in
                       FStar_All.pipe_right uu____2825 FStar_Util.must  in
                     let r =
                       (FStar_Pervasives_Native.snd if_then_else_ts).FStar_Syntax_Syntax.pos
                        in
                     let uu____2853 =
                       check_and_gen1 "if_then_else" Prims.int_one
                         if_then_else_ts
                        in
                     match uu____2853 with
                     | (if_then_else_us,if_then_else_t,if_then_else_ty) ->
                         let uu____2877 =
                           FStar_Syntax_Subst.open_univ_vars if_then_else_us
                             if_then_else_t
                            in
                         (match uu____2877 with
                          | (us,t) ->
                              let uu____2896 =
                                FStar_Syntax_Subst.open_univ_vars
                                  if_then_else_us if_then_else_ty
                                 in
                              (match uu____2896 with
                               | (uu____2913,ty) ->
                                   let env =
                                     FStar_TypeChecker_Env.push_univ_vars
                                       env0 us
                                      in
                                   let uu____2916 = fresh_a_and_u_a "a"  in
                                   (match uu____2916 with
                                    | (a,u_a) ->
                                        let rest_bs =
                                          let uu____2945 =
                                            let uu____2946 =
                                              FStar_Syntax_Subst.compress ty
                                               in
                                            uu____2946.FStar_Syntax_Syntax.n
                                             in
                                          match uu____2945 with
                                          | FStar_Syntax_Syntax.Tm_arrow
                                              (bs,uu____2958) when
                                              (FStar_List.length bs) >=
                                                (Prims.of_int (4))
                                              ->
                                              let uu____2986 =
                                                FStar_Syntax_Subst.open_binders
                                                  bs
                                                 in
                                              (match uu____2986 with
                                               | (a',uu____2996)::bs1 ->
                                                   let uu____3016 =
                                                     let uu____3017 =
                                                       FStar_All.pipe_right
                                                         bs1
                                                         (FStar_List.splitAt
                                                            ((FStar_List.length
                                                                bs1)
                                                               -
                                                               (Prims.of_int (3))))
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3017
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   let uu____3115 =
                                                     let uu____3128 =
                                                       let uu____3131 =
                                                         let uu____3132 =
                                                           let uu____3139 =
                                                             let uu____3142 =
                                                               FStar_All.pipe_right
                                                                 a
                                                                 FStar_Pervasives_Native.fst
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____3142
                                                               FStar_Syntax_Syntax.bv_to_name
                                                              in
                                                           (a', uu____3139)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____3132
                                                          in
                                                       [uu____3131]  in
                                                     FStar_Syntax_Subst.subst_binders
                                                       uu____3128
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3016 uu____3115)
                                          | uu____3163 ->
                                              not_an_arrow_error
                                                "if_then_else"
                                                (Prims.of_int (4)) ty r
                                           in
                                        let bs = a :: rest_bs  in
                                        let uu____3181 =
                                          let uu____3192 =
                                            let uu____3197 =
                                              FStar_TypeChecker_Env.push_binders
                                                env bs
                                               in
                                            let uu____3198 =
                                              let uu____3199 =
                                                FStar_All.pipe_right a
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right uu____3199
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            fresh_repr r uu____3197 u_a
                                              uu____3198
                                             in
                                          match uu____3192 with
                                          | (repr1,g) ->
                                              let uu____3220 =
                                                let uu____3227 =
                                                  FStar_Syntax_Syntax.gen_bv
                                                    "f"
                                                    FStar_Pervasives_Native.None
                                                    repr1
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3227
                                                  FStar_Syntax_Syntax.mk_binder
                                                 in
                                              (uu____3220, g)
                                           in
                                        (match uu____3181 with
                                         | (f_bs,guard_f) ->
                                             let uu____3267 =
                                               let uu____3278 =
                                                 let uu____3283 =
                                                   FStar_TypeChecker_Env.push_binders
                                                     env bs
                                                    in
                                                 let uu____3284 =
                                                   let uu____3285 =
                                                     FStar_All.pipe_right a
                                                       FStar_Pervasives_Native.fst
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____3285
                                                     FStar_Syntax_Syntax.bv_to_name
                                                    in
                                                 fresh_repr r uu____3283 u_a
                                                   uu____3284
                                                  in
                                               match uu____3278 with
                                               | (repr1,g) ->
                                                   let uu____3306 =
                                                     let uu____3313 =
                                                       FStar_Syntax_Syntax.gen_bv
                                                         "g"
                                                         FStar_Pervasives_Native.None
                                                         repr1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____3313
                                                       FStar_Syntax_Syntax.mk_binder
                                                      in
                                                   (uu____3306, g)
                                                in
                                             (match uu____3267 with
                                              | (g_bs,guard_g) ->
                                                  let p_b =
                                                    let uu____3360 =
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "p"
                                                        FStar_Pervasives_Native.None
                                                        FStar_Syntax_Util.ktype0
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____3360
                                                      FStar_Syntax_Syntax.mk_binder
                                                     in
                                                  let uu____3368 =
                                                    let uu____3373 =
                                                      FStar_TypeChecker_Env.push_binders
                                                        env
                                                        (FStar_List.append bs
                                                           [p_b])
                                                       in
                                                    let uu____3392 =
                                                      let uu____3393 =
                                                        FStar_All.pipe_right
                                                          a
                                                          FStar_Pervasives_Native.fst
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____3393
                                                        FStar_Syntax_Syntax.bv_to_name
                                                       in
                                                    fresh_repr r uu____3373
                                                      u_a uu____3392
                                                     in
                                                  (match uu____3368 with
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
                                                        (let k1 =
                                                           FStar_All.pipe_right
                                                             k
                                                             (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                                env)
                                                            in
                                                         check_no_subtyping_for_layered_combinator
                                                           env k1
                                                           (FStar_Pervasives_Native.Some
                                                              ty);
                                                         (let uu____3455 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              if_then_else_us
                                                              k1
                                                             in
                                                          (if_then_else_us,
                                                            uu____3455,
                                                            if_then_else_ty))))))))))
                      in
                   log_combinator "if_then_else" if_then_else1;
                   (let r =
                      let uu____3468 =
                        let uu____3471 =
                          let uu____3480 =
                            FStar_All.pipe_right ed
                              FStar_Syntax_Util.get_layered_if_then_else_combinator
                             in
                          FStar_All.pipe_right uu____3480 FStar_Util.must  in
                        FStar_All.pipe_right uu____3471
                          FStar_Pervasives_Native.snd
                         in
                      uu____3468.FStar_Syntax_Syntax.pos  in
                    let uu____3541 = if_then_else1  in
                    match uu____3541 with
                    | (ite_us,ite_t,uu____3556) ->
                        let uu____3569 =
                          FStar_Syntax_Subst.open_univ_vars ite_us ite_t  in
                        (match uu____3569 with
                         | (us,ite_t1) ->
                             let uu____3576 =
                               let uu____3587 =
                                 let uu____3588 =
                                   FStar_Syntax_Subst.compress ite_t1  in
                                 uu____3588.FStar_Syntax_Syntax.n  in
                               match uu____3587 with
                               | FStar_Syntax_Syntax.Tm_abs
                                   (bs,uu____3602,uu____3603) ->
                                   let bs1 =
                                     FStar_Syntax_Subst.open_binders bs  in
                                   let uu____3629 =
                                     let uu____3636 =
                                       let uu____3639 =
                                         let uu____3642 =
                                           let uu____3651 =
                                             FStar_All.pipe_right bs1
                                               (FStar_List.splitAt
                                                  ((FStar_List.length bs1) -
                                                     (Prims.of_int (3))))
                                              in
                                           FStar_All.pipe_right uu____3651
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____3642
                                           (FStar_List.map
                                              FStar_Pervasives_Native.fst)
                                          in
                                       FStar_All.pipe_right uu____3639
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.bv_to_name)
                                        in
                                     FStar_All.pipe_right uu____3636
                                       (fun l  ->
                                          let uu____3795 = l  in
                                          match uu____3795 with
                                          | f::g::p::[] -> (f, g, p))
                                      in
                                   (match uu____3629 with
                                    | (f,g,p) ->
                                        let uu____3820 =
                                          let uu____3821 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env0 us
                                             in
                                          FStar_TypeChecker_Env.push_binders
                                            uu____3821 bs1
                                           in
                                        let uu____3822 =
                                          let uu____3823 =
                                            let uu____3828 =
                                              let uu____3829 =
                                                let uu____3832 =
                                                  FStar_All.pipe_right bs1
                                                    (FStar_List.map
                                                       FStar_Pervasives_Native.fst)
                                                   in
                                                FStar_All.pipe_right
                                                  uu____3832
                                                  (FStar_List.map
                                                     FStar_Syntax_Syntax.bv_to_name)
                                                 in
                                              FStar_All.pipe_right uu____3829
                                                (FStar_List.map
                                                   FStar_Syntax_Syntax.as_arg)
                                               in
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              ite_t1 uu____3828
                                             in
                                          uu____3823
                                            FStar_Pervasives_Native.None r
                                           in
                                        (uu____3820, uu____3822, f, g, p))
                               | uu____3859 ->
                                   failwith
                                     "Impossible! ite_t must have been an abstraction with at least 3 binders"
                                in
                             (match uu____3576 with
                              | (env,ite_t_applied,f_t,g_t,p_t) ->
                                  let uu____3876 =
                                    let uu____3885 = stronger_repr  in
                                    match uu____3885 with
                                    | (uu____3906,subcomp_t,subcomp_ty) ->
                                        let uu____3921 =
                                          FStar_Syntax_Subst.open_univ_vars
                                            us subcomp_t
                                           in
                                        (match uu____3921 with
                                         | (uu____3934,subcomp_t1) ->
                                             let bs_except_last =
                                               let uu____3945 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   us subcomp_ty
                                                  in
                                               match uu____3945 with
                                               | (uu____3958,subcomp_ty1) ->
                                                   let uu____3960 =
                                                     let uu____3961 =
                                                       FStar_Syntax_Subst.compress
                                                         subcomp_ty1
                                                        in
                                                     uu____3961.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____3960 with
                                                    | FStar_Syntax_Syntax.Tm_arrow
                                                        (bs,uu____3973) ->
                                                        let uu____3994 =
                                                          FStar_All.pipe_right
                                                            bs
                                                            (FStar_List.splitAt
                                                               ((FStar_List.length
                                                                   bs)
                                                                  -
                                                                  Prims.int_one))
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____3994
                                                          FStar_Pervasives_Native.fst
                                                    | uu____4100 ->
                                                        failwith
                                                          "Impossible! subcomp_ty must have been an arrow with at lease 1 binder")
                                                in
                                             let aux t =
                                               let uu____4118 =
                                                 let uu____4123 =
                                                   let uu____4124 =
                                                     let uu____4127 =
                                                       FStar_All.pipe_right
                                                         bs_except_last
                                                         (FStar_List.map
                                                            (fun uu____4147 
                                                               ->
                                                               FStar_Syntax_Syntax.tun))
                                                        in
                                                     FStar_List.append
                                                       uu____4127 [t]
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____4124
                                                     (FStar_List.map
                                                        FStar_Syntax_Syntax.as_arg)
                                                    in
                                                 FStar_Syntax_Syntax.mk_Tm_app
                                                   subcomp_t1 uu____4123
                                                  in
                                               uu____4118
                                                 FStar_Pervasives_Native.None
                                                 r
                                                in
                                             let uu____4156 = aux f_t  in
                                             let uu____4159 = aux g_t  in
                                             (uu____4156, uu____4159))
                                     in
                                  (match uu____3876 with
                                   | (subcomp_f,subcomp_g) ->
                                       let uu____4176 =
                                         let aux t =
                                           let uu____4193 =
                                             let uu____4200 =
                                               let uu____4201 =
                                                 let uu____4228 =
                                                   let uu____4245 =
                                                     let uu____4254 =
                                                       FStar_Syntax_Syntax.mk_Total
                                                         ite_t_applied
                                                        in
                                                     FStar_Util.Inr
                                                       uu____4254
                                                      in
                                                   (uu____4245,
                                                     FStar_Pervasives_Native.None)
                                                    in
                                                 (t, uu____4228,
                                                   FStar_Pervasives_Native.None)
                                                  in
                                               FStar_Syntax_Syntax.Tm_ascribed
                                                 uu____4201
                                                in
                                             FStar_Syntax_Syntax.mk
                                               uu____4200
                                              in
                                           uu____4193
                                             FStar_Pervasives_Native.None r
                                            in
                                         let uu____4295 = aux subcomp_f  in
                                         let uu____4296 = aux subcomp_g  in
                                         (uu____4295, uu____4296)  in
                                       (match uu____4176 with
                                        | (tm_subcomp_ascribed_f,tm_subcomp_ascribed_g)
                                            ->
                                            ((let uu____4300 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4300
                                              then
                                                let uu____4305 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_f
                                                   in
                                                let uu____4307 =
                                                  FStar_Syntax_Print.term_to_string
                                                    tm_subcomp_ascribed_g
                                                   in
                                                FStar_Util.print2
                                                  "Checking the soundness of the if_then_else combinators, f: %s, g: %s\n"
                                                  uu____4305 uu____4307
                                              else ());
                                             (let uu____4312 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env tm_subcomp_ascribed_f
                                                 in
                                              match uu____4312 with
                                              | (uu____4319,uu____4320,g_f)
                                                  ->
                                                  let g_f1 =
                                                    let uu____4323 =
                                                      FStar_TypeChecker_Env.guard_of_guard_formula
                                                        (FStar_TypeChecker_Common.NonTrivial
                                                           p_t)
                                                       in
                                                    FStar_TypeChecker_Env.imp_guard
                                                      uu____4323 g_f
                                                     in
                                                  (FStar_TypeChecker_Rel.force_trivial_guard
                                                     env g_f1;
                                                   (let uu____4325 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env
                                                        tm_subcomp_ascribed_g
                                                       in
                                                    match uu____4325 with
                                                    | (uu____4332,uu____4333,g_g)
                                                        ->
                                                        let g_g1 =
                                                          let not_p =
                                                            let uu____4339 =
                                                              let uu____4344
                                                                =
                                                                let uu____4345
                                                                  =
                                                                  FStar_Syntax_Syntax.lid_as_fv
                                                                    FStar_Parser_Const.not_lid
                                                                    FStar_Syntax_Syntax.delta_constant
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                FStar_All.pipe_right
                                                                  uu____4345
                                                                  FStar_Syntax_Syntax.fv_to_tm
                                                                 in
                                                              let uu____4346
                                                                =
                                                                let uu____4347
                                                                  =
                                                                  FStar_All.pipe_right
                                                                    p_t
                                                                    FStar_Syntax_Syntax.as_arg
                                                                   in
                                                                [uu____4347]
                                                                 in
                                                              FStar_Syntax_Syntax.mk_Tm_app
                                                                uu____4344
                                                                uu____4346
                                                               in
                                                            uu____4339
                                                              FStar_Pervasives_Native.None
                                                              r
                                                             in
                                                          let uu____4380 =
                                                            FStar_TypeChecker_Env.guard_of_guard_formula
                                                              (FStar_TypeChecker_Common.NonTrivial
                                                                 not_p)
                                                             in
                                                          FStar_TypeChecker_Env.imp_guard
                                                            uu____4380 g_g
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
                        (let uu____4404 =
                           let uu____4410 =
                             let uu____4412 =
                               FStar_Syntax_Print.binders_to_string "; "
                                 act.FStar_Syntax_Syntax.action_params
                                in
                             FStar_Util.format3
                               "Action %s:%s has non-empty action params (%s)"
                               (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                               (act.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                               uu____4412
                              in
                           (FStar_Errors.Fatal_MalformedActionDeclaration,
                             uu____4410)
                            in
                         FStar_Errors.raise_error uu____4404 r)
                      else ();
                      (let uu____4419 =
                         let uu____4424 =
                           FStar_Syntax_Subst.univ_var_opening
                             act.FStar_Syntax_Syntax.action_univs
                            in
                         match uu____4424 with
                         | (usubst,us) ->
                             let uu____4447 =
                               FStar_TypeChecker_Env.push_univ_vars env us
                                in
                             let uu____4448 =
                               let uu___448_4449 = act  in
                               let uu____4450 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_defn
                                  in
                               let uu____4451 =
                                 FStar_Syntax_Subst.subst usubst
                                   act.FStar_Syntax_Syntax.action_typ
                                  in
                               {
                                 FStar_Syntax_Syntax.action_name =
                                   (uu___448_4449.FStar_Syntax_Syntax.action_name);
                                 FStar_Syntax_Syntax.action_unqualified_name
                                   =
                                   (uu___448_4449.FStar_Syntax_Syntax.action_unqualified_name);
                                 FStar_Syntax_Syntax.action_univs = us;
                                 FStar_Syntax_Syntax.action_params =
                                   (uu___448_4449.FStar_Syntax_Syntax.action_params);
                                 FStar_Syntax_Syntax.action_defn = uu____4450;
                                 FStar_Syntax_Syntax.action_typ = uu____4451
                               }  in
                             (uu____4447, uu____4448)
                          in
                       match uu____4419 with
                       | (env1,act1) ->
                           let act_typ =
                             let uu____4455 =
                               let uu____4456 =
                                 FStar_Syntax_Subst.compress
                                   act1.FStar_Syntax_Syntax.action_typ
                                  in
                               uu____4456.FStar_Syntax_Syntax.n  in
                             match uu____4455 with
                             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                                 let ct =
                                   FStar_Syntax_Util.comp_to_comp_typ c  in
                                 let uu____4482 =
                                   FStar_Ident.lid_equals
                                     ct.FStar_Syntax_Syntax.effect_name
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 if uu____4482
                                 then
                                   let repr_ts =
                                     let uu____4486 = repr  in
                                     match uu____4486 with
                                     | (us,t,uu____4501) -> (us, t)  in
                                   let repr1 =
                                     let uu____4519 =
                                       FStar_TypeChecker_Env.inst_tscheme_with
                                         repr_ts
                                         ct.FStar_Syntax_Syntax.comp_univs
                                        in
                                     FStar_All.pipe_right uu____4519
                                       FStar_Pervasives_Native.snd
                                      in
                                   let repr2 =
                                     let uu____4531 =
                                       let uu____4536 =
                                         let uu____4537 =
                                           FStar_Syntax_Syntax.as_arg
                                             ct.FStar_Syntax_Syntax.result_typ
                                            in
                                         uu____4537 ::
                                           (ct.FStar_Syntax_Syntax.effect_args)
                                          in
                                       FStar_Syntax_Syntax.mk_Tm_app repr1
                                         uu____4536
                                        in
                                     uu____4531 FStar_Pervasives_Native.None
                                       r
                                      in
                                   let c1 =
                                     let uu____4555 =
                                       let uu____4558 =
                                         FStar_TypeChecker_Env.new_u_univ ()
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____4558
                                        in
                                     FStar_Syntax_Syntax.mk_Total' repr2
                                       uu____4555
                                      in
                                   FStar_Syntax_Util.arrow bs c1
                                 else act1.FStar_Syntax_Syntax.action_typ
                             | uu____4561 ->
                                 act1.FStar_Syntax_Syntax.action_typ
                              in
                           let uu____4562 =
                             FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                               env1 act_typ
                              in
                           (match uu____4562 with
                            | (act_typ1,uu____4570,g_t) ->
                                let uu____4572 =
                                  let uu____4579 =
                                    let uu___473_4580 =
                                      FStar_TypeChecker_Env.set_expected_typ
                                        env1 act_typ1
                                       in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___473_4580.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___473_4580.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___473_4580.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___473_4580.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___473_4580.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___473_4580.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___473_4580.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___473_4580.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___473_4580.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___473_4580.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        false;
                                      FStar_TypeChecker_Env.effects =
                                        (uu___473_4580.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___473_4580.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___473_4580.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___473_4580.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        (uu___473_4580.FStar_TypeChecker_Env.check_uvars);
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___473_4580.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___473_4580.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___473_4580.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___473_4580.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___473_4580.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___473_4580.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___473_4580.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___473_4580.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___473_4580.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___473_4580.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___473_4580.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___473_4580.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___473_4580.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___473_4580.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___473_4580.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___473_4580.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___473_4580.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___473_4580.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___473_4580.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___473_4580.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.mpreprocess =
                                        (uu___473_4580.FStar_TypeChecker_Env.mpreprocess);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___473_4580.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___473_4580.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___473_4580.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___473_4580.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___473_4580.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___473_4580.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___473_4580.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___473_4580.FStar_TypeChecker_Env.erasable_types_tab)
                                    }  in
                                  FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                    uu____4579
                                    act1.FStar_Syntax_Syntax.action_defn
                                   in
                                (match uu____4572 with
                                 | (act_defn,uu____4583,g_d) ->
                                     ((let uu____4586 =
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.debug env1)
                                           (FStar_Options.Other
                                              "LayeredEffects")
                                          in
                                       if uu____4586
                                       then
                                         let uu____4591 =
                                           FStar_Syntax_Print.term_to_string
                                             act_defn
                                            in
                                         let uu____4593 =
                                           FStar_Syntax_Print.term_to_string
                                             act_typ1
                                            in
                                         FStar_Util.print2
                                           "Typechecked action definition: %s and action type: %s\n"
                                           uu____4591 uu____4593
                                       else ());
                                      (let uu____4598 =
                                         let act_typ2 =
                                           FStar_TypeChecker_Normalize.normalize
                                             [FStar_TypeChecker_Env.Beta]
                                             env1 act_typ1
                                            in
                                         let uu____4606 =
                                           let uu____4607 =
                                             FStar_Syntax_Subst.compress
                                               act_typ2
                                              in
                                           uu____4607.FStar_Syntax_Syntax.n
                                            in
                                         match uu____4606 with
                                         | FStar_Syntax_Syntax.Tm_arrow
                                             (bs,uu____4617) ->
                                             let bs1 =
                                               FStar_Syntax_Subst.open_binders
                                                 bs
                                                in
                                             let env2 =
                                               FStar_TypeChecker_Env.push_binders
                                                 env1 bs1
                                                in
                                             let uu____4640 =
                                               FStar_Syntax_Util.type_u ()
                                                in
                                             (match uu____4640 with
                                              | (t,u) ->
                                                  let reason =
                                                    FStar_Util.format2
                                                      "implicit for return type of action %s:%s"
                                                      (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                      (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                     in
                                                  let uu____4656 =
                                                    FStar_TypeChecker_Util.new_implicit_var
                                                      reason r env2 t
                                                     in
                                                  (match uu____4656 with
                                                   | (a_tm,uu____4676,g_tm)
                                                       ->
                                                       let uu____4690 =
                                                         fresh_repr r env2 u
                                                           a_tm
                                                          in
                                                       (match uu____4690 with
                                                        | (repr1,g) ->
                                                            let uu____4703 =
                                                              let uu____4706
                                                                =
                                                                let uu____4709
                                                                  =
                                                                  let uu____4712
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                  FStar_All.pipe_right
                                                                    uu____4712
                                                                    (
                                                                    fun _4715
                                                                     ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _4715)
                                                                   in
                                                                FStar_Syntax_Syntax.mk_Total'
                                                                  repr1
                                                                  uu____4709
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4706
                                                               in
                                                            let uu____4716 =
                                                              FStar_TypeChecker_Env.conj_guard
                                                                g g_tm
                                                               in
                                                            (uu____4703,
                                                              uu____4716))))
                                         | uu____4719 ->
                                             let uu____4720 =
                                               let uu____4726 =
                                                 let uu____4728 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.format3
                                                   "Unexpected non-function type for action %s:%s (%s)"
                                                   (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                   (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                   uu____4728
                                                  in
                                               (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                 uu____4726)
                                                in
                                             FStar_Errors.raise_error
                                               uu____4720 r
                                          in
                                       match uu____4598 with
                                       | (k,g_k) ->
                                           ((let uu____4745 =
                                               FStar_All.pipe_left
                                                 (FStar_TypeChecker_Env.debug
                                                    env1)
                                                 (FStar_Options.Other
                                                    "LayeredEffects")
                                                in
                                             if uu____4745
                                             then
                                               let uu____4750 =
                                                 FStar_Syntax_Print.term_to_string
                                                   k
                                                  in
                                               FStar_Util.print1
                                                 "Expected action type: %s\n"
                                                 uu____4750
                                             else ());
                                            (let g =
                                               FStar_TypeChecker_Rel.teq env1
                                                 act_typ1 k
                                                in
                                             FStar_List.iter
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1) [g_t; g_d; g_k; g];
                                             (let uu____4758 =
                                                FStar_All.pipe_left
                                                  (FStar_TypeChecker_Env.debug
                                                     env1)
                                                  (FStar_Options.Other
                                                     "LayeredEffects")
                                                 in
                                              if uu____4758
                                              then
                                                let uu____4763 =
                                                  FStar_Syntax_Print.term_to_string
                                                    k
                                                   in
                                                FStar_Util.print1
                                                  "Expected action type after unification: %s\n"
                                                  uu____4763
                                              else ());
                                             (let act_typ2 =
                                                let err_msg t =
                                                  let uu____4776 =
                                                    FStar_Syntax_Print.term_to_string
                                                      t
                                                     in
                                                  FStar_Util.format3
                                                    "Unexpected (k-)type of action %s:%s, expected bs -> repr<u> i_1 ... i_n, found: %s"
                                                    (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                    (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                    uu____4776
                                                   in
                                                let repr_args t =
                                                  let uu____4797 =
                                                    let uu____4798 =
                                                      FStar_Syntax_Subst.compress
                                                        t
                                                       in
                                                    uu____4798.FStar_Syntax_Syntax.n
                                                     in
                                                  match uu____4797 with
                                                  | FStar_Syntax_Syntax.Tm_app
                                                      (head1,a::is) ->
                                                      let uu____4850 =
                                                        let uu____4851 =
                                                          FStar_Syntax_Subst.compress
                                                            head1
                                                           in
                                                        uu____4851.FStar_Syntax_Syntax.n
                                                         in
                                                      (match uu____4850 with
                                                       | FStar_Syntax_Syntax.Tm_uinst
                                                           (uu____4860,us) ->
                                                           (us,
                                                             (FStar_Pervasives_Native.fst
                                                                a), is)
                                                       | uu____4870 ->
                                                           let uu____4871 =
                                                             let uu____4877 =
                                                               err_msg t  in
                                                             (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                               uu____4877)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____4871 r)
                                                  | uu____4886 ->
                                                      let uu____4887 =
                                                        let uu____4893 =
                                                          err_msg t  in
                                                        (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                          uu____4893)
                                                         in
                                                      FStar_Errors.raise_error
                                                        uu____4887 r
                                                   in
                                                let k1 =
                                                  FStar_TypeChecker_Normalize.normalize
                                                    [FStar_TypeChecker_Env.Beta]
                                                    env1 k
                                                   in
                                                let uu____4903 =
                                                  let uu____4904 =
                                                    FStar_Syntax_Subst.compress
                                                      k1
                                                     in
                                                  uu____4904.FStar_Syntax_Syntax.n
                                                   in
                                                match uu____4903 with
                                                | FStar_Syntax_Syntax.Tm_arrow
                                                    (bs,c) ->
                                                    let uu____4929 =
                                                      FStar_Syntax_Subst.open_comp
                                                        bs c
                                                       in
                                                    (match uu____4929 with
                                                     | (bs1,c1) ->
                                                         let uu____4936 =
                                                           repr_args
                                                             (FStar_Syntax_Util.comp_result
                                                                c1)
                                                            in
                                                         (match uu____4936
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
                                                              let uu____4947
                                                                =
                                                                FStar_Syntax_Syntax.mk_Comp
                                                                  ct
                                                                 in
                                                              FStar_Syntax_Util.arrow
                                                                bs1
                                                                uu____4947))
                                                | uu____4950 ->
                                                    let uu____4951 =
                                                      let uu____4957 =
                                                        err_msg k1  in
                                                      (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                        uu____4957)
                                                       in
                                                    FStar_Errors.raise_error
                                                      uu____4951 r
                                                 in
                                              (let uu____4961 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env1)
                                                   (FStar_Options.Other
                                                      "LayeredEffects")
                                                  in
                                               if uu____4961
                                               then
                                                 let uu____4966 =
                                                   FStar_Syntax_Print.term_to_string
                                                     act_typ2
                                                    in
                                                 FStar_Util.print1
                                                   "Action type after injecting it into the monad: %s\n"
                                                   uu____4966
                                               else ());
                                              (let act2 =
                                                 let uu____4972 =
                                                   FStar_TypeChecker_Util.generalize_universes
                                                     env1 act_defn
                                                    in
                                                 match uu____4972 with
                                                 | (us,act_defn1) ->
                                                     if
                                                       act1.FStar_Syntax_Syntax.action_univs
                                                         = []
                                                     then
                                                       let uu___546_4986 =
                                                         act1  in
                                                       let uu____4987 =
                                                         FStar_Syntax_Subst.close_univ_vars
                                                           us act_typ2
                                                          in
                                                       {
                                                         FStar_Syntax_Syntax.action_name
                                                           =
                                                           (uu___546_4986.FStar_Syntax_Syntax.action_name);
                                                         FStar_Syntax_Syntax.action_unqualified_name
                                                           =
                                                           (uu___546_4986.FStar_Syntax_Syntax.action_unqualified_name);
                                                         FStar_Syntax_Syntax.action_univs
                                                           = us;
                                                         FStar_Syntax_Syntax.action_params
                                                           =
                                                           (uu___546_4986.FStar_Syntax_Syntax.action_params);
                                                         FStar_Syntax_Syntax.action_defn
                                                           = act_defn1;
                                                         FStar_Syntax_Syntax.action_typ
                                                           = uu____4987
                                                       }
                                                     else
                                                       (let uu____4990 =
                                                          ((FStar_List.length
                                                              us)
                                                             =
                                                             (FStar_List.length
                                                                act1.FStar_Syntax_Syntax.action_univs))
                                                            &&
                                                            (FStar_List.forall2
                                                               (fun u1  ->
                                                                  fun u2  ->
                                                                    let uu____4997
                                                                    =
                                                                    FStar_Syntax_Syntax.order_univ_name
                                                                    u1 u2  in
                                                                    uu____4997
                                                                    =
                                                                    Prims.int_zero)
                                                               us
                                                               act1.FStar_Syntax_Syntax.action_univs)
                                                           in
                                                        if uu____4990
                                                        then
                                                          let uu___551_5002 =
                                                            act1  in
                                                          let uu____5003 =
                                                            FStar_Syntax_Subst.close_univ_vars
                                                              act1.FStar_Syntax_Syntax.action_univs
                                                              act_typ2
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___551_5002.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___551_5002.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              =
                                                              (uu___551_5002.FStar_Syntax_Syntax.action_univs);
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___551_5002.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = act_defn1;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____5003
                                                          }
                                                        else
                                                          (let uu____5006 =
                                                             let uu____5012 =
                                                               let uu____5014
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   us
                                                                  in
                                                               let uu____5016
                                                                 =
                                                                 FStar_Syntax_Print.univ_names_to_string
                                                                   act1.FStar_Syntax_Syntax.action_univs
                                                                  in
                                                               FStar_Util.format4
                                                                 "Expected and generalized universes in the declaration for %s:%s are different, input: %s, but after gen: %s"
                                                                 (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                                 (act1.FStar_Syntax_Syntax.action_name).FStar_Ident.str
                                                                 uu____5014
                                                                 uu____5016
                                                                in
                                                             (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                               uu____5012)
                                                              in
                                                           FStar_Errors.raise_error
                                                             uu____5006 r))
                                                  in
                                               act2)))))))))
                       in
                    let tschemes_of uu____5041 =
                      match uu____5041 with
                      | (us,t,ty) -> ((us, t), (us, ty))  in
                    let combinators =
                      let uu____5086 =
                        let uu____5087 = tschemes_of repr  in
                        let uu____5092 = tschemes_of return_repr  in
                        let uu____5097 = tschemes_of bind_repr  in
                        let uu____5102 = tschemes_of stronger_repr  in
                        let uu____5107 = tschemes_of if_then_else1  in
                        {
                          FStar_Syntax_Syntax.l_base_effect =
                            underlying_effect_lid;
                          FStar_Syntax_Syntax.l_repr = uu____5087;
                          FStar_Syntax_Syntax.l_return = uu____5092;
                          FStar_Syntax_Syntax.l_bind = uu____5097;
                          FStar_Syntax_Syntax.l_subcomp = uu____5102;
                          FStar_Syntax_Syntax.l_if_then_else = uu____5107
                        }  in
                      FStar_Syntax_Syntax.Layered_eff uu____5086  in
                    let uu___560_5112 = ed  in
                    let uu____5113 =
                      FStar_List.map (tc_action env0)
                        ed.FStar_Syntax_Syntax.actions
                       in
                    {
                      FStar_Syntax_Syntax.mname =
                        (uu___560_5112.FStar_Syntax_Syntax.mname);
                      FStar_Syntax_Syntax.cattributes =
                        (uu___560_5112.FStar_Syntax_Syntax.cattributes);
                      FStar_Syntax_Syntax.univs =
                        (uu___560_5112.FStar_Syntax_Syntax.univs);
                      FStar_Syntax_Syntax.binders =
                        (uu___560_5112.FStar_Syntax_Syntax.binders);
                      FStar_Syntax_Syntax.signature =
                        (let uu____5120 = signature  in
                         match uu____5120 with | (us,t,uu____5135) -> (us, t));
                      FStar_Syntax_Syntax.combinators = combinators;
                      FStar_Syntax_Syntax.actions = uu____5113;
                      FStar_Syntax_Syntax.eff_attrs =
                        (uu___560_5112.FStar_Syntax_Syntax.eff_attrs)
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
        (let uu____5173 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
             (FStar_Options.Other "ED")
            in
         if uu____5173
         then
           let uu____5178 = FStar_Syntax_Print.eff_decl_to_string false ed
              in
           FStar_Util.print1 "Typechecking eff_decl: \n\t%s\n" uu____5178
         else ());
        (let uu____5184 =
           let uu____5189 =
             FStar_Syntax_Subst.univ_var_opening ed.FStar_Syntax_Syntax.univs
              in
           match uu____5189 with
           | (ed_univs_subst,ed_univs) ->
               let bs =
                 let uu____5213 =
                   FStar_Syntax_Subst.subst_binders ed_univs_subst
                     ed.FStar_Syntax_Syntax.binders
                    in
                 FStar_Syntax_Subst.open_binders uu____5213  in
               let uu____5214 =
                 let uu____5221 =
                   FStar_TypeChecker_Env.push_univ_vars env0 ed_univs  in
                 FStar_TypeChecker_TcTerm.tc_tparams uu____5221 bs  in
               (match uu____5214 with
                | (bs1,uu____5227,uu____5228) ->
                    let uu____5229 =
                      let tmp_t =
                        let uu____5239 =
                          let uu____5242 =
                            FStar_All.pipe_right FStar_Syntax_Syntax.U_zero
                              (fun _5247  ->
                                 FStar_Pervasives_Native.Some _5247)
                             in
                          FStar_Syntax_Syntax.mk_Total'
                            FStar_Syntax_Syntax.t_unit uu____5242
                           in
                        FStar_Syntax_Util.arrow bs1 uu____5239  in
                      let uu____5248 =
                        FStar_TypeChecker_Util.generalize_universes env0
                          tmp_t
                         in
                      match uu____5248 with
                      | (us,tmp_t1) ->
                          let uu____5265 =
                            let uu____5266 =
                              let uu____5267 =
                                FStar_All.pipe_right tmp_t1
                                  FStar_Syntax_Util.arrow_formals
                                 in
                              FStar_All.pipe_right uu____5267
                                FStar_Pervasives_Native.fst
                               in
                            FStar_All.pipe_right uu____5266
                              FStar_Syntax_Subst.close_binders
                             in
                          (us, uu____5265)
                       in
                    (match uu____5229 with
                     | (us,bs2) ->
                         (match ed_univs with
                          | [] -> (us, bs2)
                          | uu____5304 ->
                              let uu____5307 =
                                ((FStar_List.length ed_univs) =
                                   (FStar_List.length us))
                                  &&
                                  (FStar_List.forall2
                                     (fun u1  ->
                                        fun u2  ->
                                          let uu____5314 =
                                            FStar_Syntax_Syntax.order_univ_name
                                              u1 u2
                                             in
                                          uu____5314 = Prims.int_zero)
                                     ed_univs us)
                                 in
                              if uu____5307
                              then (us, bs2)
                              else
                                (let uu____5325 =
                                   let uu____5331 =
                                     let uu____5333 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length ed_univs)
                                        in
                                     let uu____5335 =
                                       FStar_Util.string_of_int
                                         (FStar_List.length us)
                                        in
                                     FStar_Util.format3
                                       "Expected and generalized universes in effect declaration for %s are different, expected: %s, but found %s"
                                       (ed.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                       uu____5333 uu____5335
                                      in
                                   (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                     uu____5331)
                                    in
                                 let uu____5339 =
                                   FStar_Ident.range_of_lid
                                     ed.FStar_Syntax_Syntax.mname
                                    in
                                 FStar_Errors.raise_error uu____5325
                                   uu____5339))))
            in
         match uu____5184 with
         | (us,bs) ->
             let ed1 =
               let uu___594_5347 = ed  in
               {
                 FStar_Syntax_Syntax.mname =
                   (uu___594_5347.FStar_Syntax_Syntax.mname);
                 FStar_Syntax_Syntax.cattributes =
                   (uu___594_5347.FStar_Syntax_Syntax.cattributes);
                 FStar_Syntax_Syntax.univs = us;
                 FStar_Syntax_Syntax.binders = bs;
                 FStar_Syntax_Syntax.signature =
                   (uu___594_5347.FStar_Syntax_Syntax.signature);
                 FStar_Syntax_Syntax.combinators =
                   (uu___594_5347.FStar_Syntax_Syntax.combinators);
                 FStar_Syntax_Syntax.actions =
                   (uu___594_5347.FStar_Syntax_Syntax.actions);
                 FStar_Syntax_Syntax.eff_attrs =
                   (uu___594_5347.FStar_Syntax_Syntax.eff_attrs)
               }  in
             let uu____5348 = FStar_Syntax_Subst.univ_var_opening us  in
             (match uu____5348 with
              | (ed_univs_subst,ed_univs) ->
                  let uu____5367 =
                    let uu____5372 =
                      FStar_Syntax_Subst.subst_binders ed_univs_subst bs  in
                    FStar_Syntax_Subst.open_binders' uu____5372  in
                  (match uu____5367 with
                   | (ed_bs,ed_bs_subst) ->
                       let ed2 =
                         let op uu____5393 =
                           match uu____5393 with
                           | (us1,t) ->
                               let t1 =
                                 let uu____5413 =
                                   FStar_Syntax_Subst.shift_subst
                                     ((FStar_List.length ed_bs) +
                                        (FStar_List.length us1))
                                     ed_univs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5413 t  in
                               let uu____5422 =
                                 let uu____5423 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length us1) ed_bs_subst
                                    in
                                 FStar_Syntax_Subst.subst uu____5423 t1  in
                               (us1, uu____5422)
                            in
                         let uu___608_5428 = ed1  in
                         let uu____5429 =
                           op ed1.FStar_Syntax_Syntax.signature  in
                         let uu____5430 =
                           FStar_Syntax_Util.apply_eff_combinators op
                             ed1.FStar_Syntax_Syntax.combinators
                            in
                         let uu____5431 =
                           FStar_List.map
                             (fun a  ->
                                let uu___611_5439 = a  in
                                let uu____5440 =
                                  let uu____5441 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_defn))
                                     in
                                  FStar_Pervasives_Native.snd uu____5441  in
                                let uu____5452 =
                                  let uu____5453 =
                                    op
                                      ((a.FStar_Syntax_Syntax.action_univs),
                                        (a.FStar_Syntax_Syntax.action_typ))
                                     in
                                  FStar_Pervasives_Native.snd uu____5453  in
                                {
                                  FStar_Syntax_Syntax.action_name =
                                    (uu___611_5439.FStar_Syntax_Syntax.action_name);
                                  FStar_Syntax_Syntax.action_unqualified_name
                                    =
                                    (uu___611_5439.FStar_Syntax_Syntax.action_unqualified_name);
                                  FStar_Syntax_Syntax.action_univs =
                                    (uu___611_5439.FStar_Syntax_Syntax.action_univs);
                                  FStar_Syntax_Syntax.action_params =
                                    (uu___611_5439.FStar_Syntax_Syntax.action_params);
                                  FStar_Syntax_Syntax.action_defn =
                                    uu____5440;
                                  FStar_Syntax_Syntax.action_typ = uu____5452
                                }) ed1.FStar_Syntax_Syntax.actions
                            in
                         {
                           FStar_Syntax_Syntax.mname =
                             (uu___608_5428.FStar_Syntax_Syntax.mname);
                           FStar_Syntax_Syntax.cattributes =
                             (uu___608_5428.FStar_Syntax_Syntax.cattributes);
                           FStar_Syntax_Syntax.univs =
                             (uu___608_5428.FStar_Syntax_Syntax.univs);
                           FStar_Syntax_Syntax.binders =
                             (uu___608_5428.FStar_Syntax_Syntax.binders);
                           FStar_Syntax_Syntax.signature = uu____5429;
                           FStar_Syntax_Syntax.combinators = uu____5430;
                           FStar_Syntax_Syntax.actions = uu____5431;
                           FStar_Syntax_Syntax.eff_attrs =
                             (uu___608_5428.FStar_Syntax_Syntax.eff_attrs)
                         }  in
                       ((let uu____5465 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env0)
                             (FStar_Options.Other "ED")
                            in
                         if uu____5465
                         then
                           let uu____5470 =
                             FStar_Syntax_Print.eff_decl_to_string false ed2
                              in
                           FStar_Util.print1
                             "After typechecking binders eff_decl: \n\t%s\n"
                             uu____5470
                         else ());
                        (let env =
                           let uu____5477 =
                             FStar_TypeChecker_Env.push_univ_vars env0
                               ed_univs
                              in
                           FStar_TypeChecker_Env.push_binders uu____5477
                             ed_bs
                            in
                         let check_and_gen' comb n1 env_opt uu____5512 k =
                           match uu____5512 with
                           | (us1,t) ->
                               let env1 =
                                 if FStar_Util.is_some env_opt
                                 then
                                   FStar_All.pipe_right env_opt
                                     FStar_Util.must
                                 else env  in
                               let uu____5532 =
                                 FStar_Syntax_Subst.open_univ_vars us1 t  in
                               (match uu____5532 with
                                | (us2,t1) ->
                                    let t2 =
                                      match k with
                                      | FStar_Pervasives_Native.Some k1 ->
                                          let uu____5541 =
                                            FStar_TypeChecker_Env.push_univ_vars
                                              env1 us2
                                             in
                                          FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                            uu____5541 t1 k1
                                      | FStar_Pervasives_Native.None  ->
                                          let uu____5542 =
                                            let uu____5549 =
                                              FStar_TypeChecker_Env.push_univ_vars
                                                env1 us2
                                               in
                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                              uu____5549 t1
                                             in
                                          (match uu____5542 with
                                           | (t2,uu____5551,g) ->
                                               (FStar_TypeChecker_Rel.force_trivial_guard
                                                  env1 g;
                                                t2))
                                       in
                                    let uu____5554 =
                                      FStar_TypeChecker_Util.generalize_universes
                                        env1 t2
                                       in
                                    (match uu____5554 with
                                     | (g_us,t3) ->
                                         (if (FStar_List.length g_us) <> n1
                                          then
                                            (let error =
                                               let uu____5570 =
                                                 FStar_Util.string_of_int n1
                                                  in
                                               let uu____5572 =
                                                 let uu____5574 =
                                                   FStar_All.pipe_right g_us
                                                     FStar_List.length
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____5574
                                                   FStar_Util.string_of_int
                                                  in
                                               FStar_Util.format4
                                                 "Expected %s:%s to be universe-polymorphic in %s universes, found %s"
                                                 (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                 comb uu____5570 uu____5572
                                                in
                                             FStar_Errors.raise_error
                                               (FStar_Errors.Fatal_MismatchUniversePolymorphic,
                                                 error)
                                               t3.FStar_Syntax_Syntax.pos)
                                          else ();
                                          (match us2 with
                                           | [] -> (g_us, t3)
                                           | uu____5589 ->
                                               let uu____5590 =
                                                 ((FStar_List.length us2) =
                                                    (FStar_List.length g_us))
                                                   &&
                                                   (FStar_List.forall2
                                                      (fun u1  ->
                                                         fun u2  ->
                                                           let uu____5597 =
                                                             FStar_Syntax_Syntax.order_univ_name
                                                               u1 u2
                                                              in
                                                           uu____5597 =
                                                             Prims.int_zero)
                                                      us2 g_us)
                                                  in
                                               if uu____5590
                                               then (g_us, t3)
                                               else
                                                 (let uu____5608 =
                                                    let uu____5614 =
                                                      let uu____5616 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             us2)
                                                         in
                                                      let uu____5618 =
                                                        FStar_Util.string_of_int
                                                          (FStar_List.length
                                                             g_us)
                                                         in
                                                      FStar_Util.format4
                                                        "Expected and generalized universes in the declaration for %s:%s are different, expected: %s, but found %s"
                                                        (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                                        comb uu____5616
                                                        uu____5618
                                                       in
                                                    (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                                                      uu____5614)
                                                     in
                                                  FStar_Errors.raise_error
                                                    uu____5608
                                                    t3.FStar_Syntax_Syntax.pos)))))
                            in
                         let signature =
                           check_and_gen' "signature" Prims.int_one
                             FStar_Pervasives_Native.None
                             ed2.FStar_Syntax_Syntax.signature
                             FStar_Pervasives_Native.None
                            in
                         (let uu____5626 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "ED")
                             in
                          if uu____5626
                          then
                            let uu____5631 =
                              FStar_Syntax_Print.tscheme_to_string signature
                               in
                            FStar_Util.print1 "Typechecked signature: %s\n"
                              uu____5631
                          else ());
                         (let fresh_a_and_wp uu____5647 =
                            let fail1 t =
                              let uu____5660 =
                                FStar_TypeChecker_Err.unexpected_signature_for_monad
                                  env ed2.FStar_Syntax_Syntax.mname t
                                 in
                              FStar_Errors.raise_error uu____5660
                                (FStar_Pervasives_Native.snd
                                   ed2.FStar_Syntax_Syntax.signature).FStar_Syntax_Syntax.pos
                               in
                            let uu____5676 =
                              FStar_TypeChecker_Env.inst_tscheme signature
                               in
                            match uu____5676 with
                            | (uu____5687,signature1) ->
                                let uu____5689 =
                                  let uu____5690 =
                                    FStar_Syntax_Subst.compress signature1
                                     in
                                  uu____5690.FStar_Syntax_Syntax.n  in
                                (match uu____5689 with
                                 | FStar_Syntax_Syntax.Tm_arrow
                                     (bs1,uu____5700) ->
                                     let bs2 =
                                       FStar_Syntax_Subst.open_binders bs1
                                        in
                                     (match bs2 with
                                      | (a,uu____5729)::(wp,uu____5731)::[]
                                          ->
                                          (a, (wp.FStar_Syntax_Syntax.sort))
                                      | uu____5760 -> fail1 signature1)
                                 | uu____5761 -> fail1 signature1)
                             in
                          let log_combinator s ts =
                            let uu____5775 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "ED")
                               in
                            if uu____5775
                            then
                              let uu____5780 =
                                FStar_Syntax_Print.tscheme_to_string ts  in
                              FStar_Util.print3 "Typechecked %s:%s = %s\n"
                                (ed2.FStar_Syntax_Syntax.mname).FStar_Ident.str
                                s uu____5780
                            else ()  in
                          let ret_wp =
                            let uu____5786 = fresh_a_and_wp ()  in
                            match uu____5786 with
                            | (a,wp_sort) ->
                                let k =
                                  let uu____5802 =
                                    let uu____5811 =
                                      FStar_Syntax_Syntax.mk_binder a  in
                                    let uu____5818 =
                                      let uu____5827 =
                                        let uu____5834 =
                                          FStar_Syntax_Syntax.bv_to_name a
                                           in
                                        FStar_Syntax_Syntax.null_binder
                                          uu____5834
                                         in
                                      [uu____5827]  in
                                    uu____5811 :: uu____5818  in
                                  let uu____5853 =
                                    FStar_Syntax_Syntax.mk_GTotal wp_sort  in
                                  FStar_Syntax_Util.arrow uu____5802
                                    uu____5853
                                   in
                                let uu____5856 =
                                  FStar_All.pipe_right ed2
                                    FStar_Syntax_Util.get_return_vc_combinator
                                   in
                                check_and_gen' "ret_wp" Prims.int_one
                                  FStar_Pervasives_Native.None uu____5856
                                  (FStar_Pervasives_Native.Some k)
                             in
                          log_combinator "ret_wp" ret_wp;
                          (let bind_wp =
                             let uu____5870 = fresh_a_and_wp ()  in
                             match uu____5870 with
                             | (a,wp_sort_a) ->
                                 let uu____5883 = fresh_a_and_wp ()  in
                                 (match uu____5883 with
                                  | (b,wp_sort_b) ->
                                      let wp_sort_a_b =
                                        let uu____5899 =
                                          let uu____5908 =
                                            let uu____5915 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                a
                                               in
                                            FStar_Syntax_Syntax.null_binder
                                              uu____5915
                                             in
                                          [uu____5908]  in
                                        let uu____5928 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5899
                                          uu____5928
                                         in
                                      let k =
                                        let uu____5934 =
                                          let uu____5943 =
                                            FStar_Syntax_Syntax.null_binder
                                              FStar_Syntax_Syntax.t_range
                                             in
                                          let uu____5950 =
                                            let uu____5959 =
                                              FStar_Syntax_Syntax.mk_binder a
                                               in
                                            let uu____5966 =
                                              let uu____5975 =
                                                FStar_Syntax_Syntax.mk_binder
                                                  b
                                                 in
                                              let uu____5982 =
                                                let uu____5991 =
                                                  FStar_Syntax_Syntax.null_binder
                                                    wp_sort_a
                                                   in
                                                let uu____5998 =
                                                  let uu____6007 =
                                                    FStar_Syntax_Syntax.null_binder
                                                      wp_sort_a_b
                                                     in
                                                  [uu____6007]  in
                                                uu____5991 :: uu____5998  in
                                              uu____5975 :: uu____5982  in
                                            uu____5959 :: uu____5966  in
                                          uu____5943 :: uu____5950  in
                                        let uu____6050 =
                                          FStar_Syntax_Syntax.mk_Total
                                            wp_sort_b
                                           in
                                        FStar_Syntax_Util.arrow uu____5934
                                          uu____6050
                                         in
                                      let uu____6053 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_bind_vc_combinator
                                         in
                                      check_and_gen' "bind_wp"
                                        (Prims.of_int (2))
                                        FStar_Pervasives_Native.None
                                        uu____6053
                                        (FStar_Pervasives_Native.Some k))
                              in
                           log_combinator "bind_wp" bind_wp;
                           (let stronger =
                              let uu____6067 = fresh_a_and_wp ()  in
                              match uu____6067 with
                              | (a,wp_sort_a) ->
                                  let uu____6080 =
                                    FStar_Syntax_Util.type_u ()  in
                                  (match uu____6080 with
                                   | (t,uu____6086) ->
                                       let k =
                                         let uu____6090 =
                                           let uu____6099 =
                                             FStar_Syntax_Syntax.mk_binder a
                                              in
                                           let uu____6106 =
                                             let uu____6115 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             let uu____6122 =
                                               let uu____6131 =
                                                 FStar_Syntax_Syntax.null_binder
                                                   wp_sort_a
                                                  in
                                               [uu____6131]  in
                                             uu____6115 :: uu____6122  in
                                           uu____6099 :: uu____6106  in
                                         let uu____6162 =
                                           FStar_Syntax_Syntax.mk_Total t  in
                                         FStar_Syntax_Util.arrow uu____6090
                                           uu____6162
                                          in
                                       let uu____6165 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_stronger_vc_combinator
                                          in
                                       check_and_gen' "stronger"
                                         Prims.int_one
                                         FStar_Pervasives_Native.None
                                         uu____6165
                                         (FStar_Pervasives_Native.Some k))
                               in
                            log_combinator "stronger" stronger;
                            (let if_then_else1 =
                               let uu____6179 = fresh_a_and_wp ()  in
                               match uu____6179 with
                               | (a,wp_sort_a) ->
                                   let p =
                                     let uu____6193 =
                                       let uu____6196 =
                                         FStar_Ident.range_of_lid
                                           ed2.FStar_Syntax_Syntax.mname
                                          in
                                       FStar_Pervasives_Native.Some
                                         uu____6196
                                        in
                                     let uu____6197 =
                                       let uu____6198 =
                                         FStar_Syntax_Util.type_u ()  in
                                       FStar_All.pipe_right uu____6198
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_Syntax_Syntax.new_bv uu____6193
                                       uu____6197
                                      in
                                   let k =
                                     let uu____6210 =
                                       let uu____6219 =
                                         FStar_Syntax_Syntax.mk_binder a  in
                                       let uu____6226 =
                                         let uu____6235 =
                                           FStar_Syntax_Syntax.mk_binder p
                                            in
                                         let uu____6242 =
                                           let uu____6251 =
                                             FStar_Syntax_Syntax.null_binder
                                               wp_sort_a
                                              in
                                           let uu____6258 =
                                             let uu____6267 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_a
                                                in
                                             [uu____6267]  in
                                           uu____6251 :: uu____6258  in
                                         uu____6235 :: uu____6242  in
                                       uu____6219 :: uu____6226  in
                                     let uu____6304 =
                                       FStar_Syntax_Syntax.mk_Total wp_sort_a
                                        in
                                     FStar_Syntax_Util.arrow uu____6210
                                       uu____6304
                                      in
                                   let uu____6307 =
                                     let uu____6312 =
                                       FStar_All.pipe_right ed2
                                         FStar_Syntax_Util.get_wp_if_then_else_combinator
                                        in
                                     FStar_All.pipe_right uu____6312
                                       FStar_Util.must
                                      in
                                   check_and_gen' "if_then_else"
                                     Prims.int_one
                                     FStar_Pervasives_Native.None uu____6307
                                     (FStar_Pervasives_Native.Some k)
                                in
                             log_combinator "if_then_else" if_then_else1;
                             (let ite_wp =
                                let uu____6344 = fresh_a_and_wp ()  in
                                match uu____6344 with
                                | (a,wp_sort_a) ->
                                    let k =
                                      let uu____6360 =
                                        let uu____6369 =
                                          FStar_Syntax_Syntax.mk_binder a  in
                                        let uu____6376 =
                                          let uu____6385 =
                                            FStar_Syntax_Syntax.null_binder
                                              wp_sort_a
                                             in
                                          [uu____6385]  in
                                        uu____6369 :: uu____6376  in
                                      let uu____6410 =
                                        FStar_Syntax_Syntax.mk_Total
                                          wp_sort_a
                                         in
                                      FStar_Syntax_Util.arrow uu____6360
                                        uu____6410
                                       in
                                    let uu____6413 =
                                      let uu____6418 =
                                        FStar_All.pipe_right ed2
                                          FStar_Syntax_Util.get_wp_ite_combinator
                                         in
                                      FStar_All.pipe_right uu____6418
                                        FStar_Util.must
                                       in
                                    check_and_gen' "ite_wp" Prims.int_one
                                      FStar_Pervasives_Native.None uu____6413
                                      (FStar_Pervasives_Native.Some k)
                                 in
                              log_combinator "ite_wp" ite_wp;
                              (let close_wp =
                                 let uu____6434 = fresh_a_and_wp ()  in
                                 match uu____6434 with
                                 | (a,wp_sort_a) ->
                                     let b =
                                       let uu____6448 =
                                         let uu____6451 =
                                           FStar_Ident.range_of_lid
                                             ed2.FStar_Syntax_Syntax.mname
                                            in
                                         FStar_Pervasives_Native.Some
                                           uu____6451
                                          in
                                       let uu____6452 =
                                         let uu____6453 =
                                           FStar_Syntax_Util.type_u ()  in
                                         FStar_All.pipe_right uu____6453
                                           FStar_Pervasives_Native.fst
                                          in
                                       FStar_Syntax_Syntax.new_bv uu____6448
                                         uu____6452
                                        in
                                     let wp_sort_b_a =
                                       let uu____6465 =
                                         let uu____6474 =
                                           let uu____6481 =
                                             FStar_Syntax_Syntax.bv_to_name b
                                              in
                                           FStar_Syntax_Syntax.null_binder
                                             uu____6481
                                            in
                                         [uu____6474]  in
                                       let uu____6494 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6465
                                         uu____6494
                                        in
                                     let k =
                                       let uu____6500 =
                                         let uu____6509 =
                                           FStar_Syntax_Syntax.mk_binder a
                                            in
                                         let uu____6516 =
                                           let uu____6525 =
                                             FStar_Syntax_Syntax.mk_binder b
                                              in
                                           let uu____6532 =
                                             let uu____6541 =
                                               FStar_Syntax_Syntax.null_binder
                                                 wp_sort_b_a
                                                in
                                             [uu____6541]  in
                                           uu____6525 :: uu____6532  in
                                         uu____6509 :: uu____6516  in
                                       let uu____6572 =
                                         FStar_Syntax_Syntax.mk_Total
                                           wp_sort_a
                                          in
                                       FStar_Syntax_Util.arrow uu____6500
                                         uu____6572
                                        in
                                     let uu____6575 =
                                       let uu____6580 =
                                         FStar_All.pipe_right ed2
                                           FStar_Syntax_Util.get_wp_close_combinator
                                          in
                                       FStar_All.pipe_right uu____6580
                                         FStar_Util.must
                                        in
                                     check_and_gen' "close_wp"
                                       (Prims.of_int (2))
                                       FStar_Pervasives_Native.None
                                       uu____6575
                                       (FStar_Pervasives_Native.Some k)
                                  in
                               log_combinator "close_wp" close_wp;
                               (let trivial =
                                  let uu____6596 = fresh_a_and_wp ()  in
                                  match uu____6596 with
                                  | (a,wp_sort_a) ->
                                      let uu____6609 =
                                        FStar_Syntax_Util.type_u ()  in
                                      (match uu____6609 with
                                       | (t,uu____6615) ->
                                           let k =
                                             let uu____6619 =
                                               let uu____6628 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   a
                                                  in
                                               let uu____6635 =
                                                 let uu____6644 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     wp_sort_a
                                                    in
                                                 [uu____6644]  in
                                               uu____6628 :: uu____6635  in
                                             let uu____6669 =
                                               FStar_Syntax_Syntax.mk_GTotal
                                                 t
                                                in
                                             FStar_Syntax_Util.arrow
                                               uu____6619 uu____6669
                                              in
                                           let trivial =
                                             let uu____6673 =
                                               let uu____6678 =
                                                 FStar_All.pipe_right ed2
                                                   FStar_Syntax_Util.get_wp_trivial_combinator
                                                  in
                                               FStar_All.pipe_right
                                                 uu____6678 FStar_Util.must
                                                in
                                             check_and_gen' "trivial"
                                               Prims.int_one
                                               FStar_Pervasives_Native.None
                                               uu____6673
                                               (FStar_Pervasives_Native.Some
                                                  k)
                                              in
                                           (log_combinator "trivial" trivial;
                                            trivial))
                                   in
                                let uu____6693 =
                                  let uu____6710 =
                                    FStar_All.pipe_right ed2
                                      FStar_Syntax_Util.get_eff_repr
                                     in
                                  match uu____6710 with
                                  | FStar_Pervasives_Native.None  ->
                                      (FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        FStar_Pervasives_Native.None,
                                        (ed2.FStar_Syntax_Syntax.actions))
                                  | uu____6739 ->
                                      let repr =
                                        let uu____6743 = fresh_a_and_wp ()
                                           in
                                        match uu____6743 with
                                        | (a,wp_sort_a) ->
                                            let uu____6756 =
                                              FStar_Syntax_Util.type_u ()  in
                                            (match uu____6756 with
                                             | (t,uu____6762) ->
                                                 let k =
                                                   let uu____6766 =
                                                     let uu____6775 =
                                                       FStar_Syntax_Syntax.mk_binder
                                                         a
                                                        in
                                                     let uu____6782 =
                                                       let uu____6791 =
                                                         FStar_Syntax_Syntax.null_binder
                                                           wp_sort_a
                                                          in
                                                       [uu____6791]  in
                                                     uu____6775 :: uu____6782
                                                      in
                                                   let uu____6816 =
                                                     FStar_Syntax_Syntax.mk_GTotal
                                                       t
                                                      in
                                                   FStar_Syntax_Util.arrow
                                                     uu____6766 uu____6816
                                                    in
                                                 let uu____6819 =
                                                   let uu____6824 =
                                                     FStar_All.pipe_right ed2
                                                       FStar_Syntax_Util.get_eff_repr
                                                      in
                                                   FStar_All.pipe_right
                                                     uu____6824
                                                     FStar_Util.must
                                                    in
                                                 check_and_gen' "repr"
                                                   Prims.int_one
                                                   FStar_Pervasives_Native.None
                                                   uu____6819
                                                   (FStar_Pervasives_Native.Some
                                                      k))
                                         in
                                      (log_combinator "repr" repr;
                                       (let mk_repr' t wp =
                                          let uu____6868 =
                                            FStar_TypeChecker_Env.inst_tscheme
                                              repr
                                             in
                                          match uu____6868 with
                                          | (uu____6875,repr1) ->
                                              let repr2 =
                                                FStar_TypeChecker_Normalize.normalize
                                                  [FStar_TypeChecker_Env.EraseUniverses;
                                                  FStar_TypeChecker_Env.AllowUnboundUniverses]
                                                  env repr1
                                                 in
                                              let uu____6878 =
                                                let uu____6885 =
                                                  let uu____6886 =
                                                    let uu____6903 =
                                                      let uu____6914 =
                                                        FStar_All.pipe_right
                                                          t
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____6931 =
                                                        let uu____6942 =
                                                          FStar_All.pipe_right
                                                            wp
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____6942]  in
                                                      uu____6914 ::
                                                        uu____6931
                                                       in
                                                    (repr2, uu____6903)  in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____6886
                                                   in
                                                FStar_Syntax_Syntax.mk
                                                  uu____6885
                                                 in
                                              uu____6878
                                                FStar_Pervasives_Native.None
                                                FStar_Range.dummyRange
                                           in
                                        let mk_repr a wp =
                                          let uu____7008 =
                                            FStar_Syntax_Syntax.bv_to_name a
                                             in
                                          mk_repr' uu____7008 wp  in
                                        let destruct_repr t =
                                          let uu____7023 =
                                            let uu____7024 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____7024.FStar_Syntax_Syntax.n
                                             in
                                          match uu____7023 with
                                          | FStar_Syntax_Syntax.Tm_app
                                              (uu____7035,(t1,uu____7037)::
                                               (wp,uu____7039)::[])
                                              -> (t1, wp)
                                          | uu____7098 ->
                                              failwith "Unexpected repr type"
                                           in
                                        let return_repr =
                                          let return_repr_ts =
                                            let uu____7114 =
                                              FStar_All.pipe_right ed2
                                                FStar_Syntax_Util.get_return_repr
                                               in
                                            FStar_All.pipe_right uu____7114
                                              FStar_Util.must
                                             in
                                          let uu____7141 = fresh_a_and_wp ()
                                             in
                                          match uu____7141 with
                                          | (a,uu____7149) ->
                                              let x_a =
                                                let uu____7155 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    a
                                                   in
                                                FStar_Syntax_Syntax.gen_bv
                                                  "x_a"
                                                  FStar_Pervasives_Native.None
                                                  uu____7155
                                                 in
                                              let res =
                                                let wp =
                                                  let uu____7163 =
                                                    let uu____7168 =
                                                      let uu____7169 =
                                                        FStar_TypeChecker_Env.inst_tscheme
                                                          ret_wp
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____7169
                                                        FStar_Pervasives_Native.snd
                                                       in
                                                    let uu____7178 =
                                                      let uu____7179 =
                                                        let uu____7188 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            a
                                                           in
                                                        FStar_All.pipe_right
                                                          uu____7188
                                                          FStar_Syntax_Syntax.as_arg
                                                         in
                                                      let uu____7197 =
                                                        let uu____7208 =
                                                          let uu____7217 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x_a
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____7217
                                                            FStar_Syntax_Syntax.as_arg
                                                           in
                                                        [uu____7208]  in
                                                      uu____7179 ::
                                                        uu____7197
                                                       in
                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                      uu____7168 uu____7178
                                                     in
                                                  uu____7163
                                                    FStar_Pervasives_Native.None
                                                    FStar_Range.dummyRange
                                                   in
                                                mk_repr a wp  in
                                              let k =
                                                let uu____7253 =
                                                  let uu____7262 =
                                                    FStar_Syntax_Syntax.mk_binder
                                                      a
                                                     in
                                                  let uu____7269 =
                                                    let uu____7278 =
                                                      FStar_Syntax_Syntax.mk_binder
                                                        x_a
                                                       in
                                                    [uu____7278]  in
                                                  uu____7262 :: uu____7269
                                                   in
                                                let uu____7303 =
                                                  FStar_Syntax_Syntax.mk_Total
                                                    res
                                                   in
                                                FStar_Syntax_Util.arrow
                                                  uu____7253 uu____7303
                                                 in
                                              let uu____7306 =
                                                FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                  env k
                                                 in
                                              (match uu____7306 with
                                               | (k1,uu____7314,uu____7315)
                                                   ->
                                                   let env1 =
                                                     let uu____7319 =
                                                       FStar_TypeChecker_Env.set_range
                                                         env
                                                         (FStar_Pervasives_Native.snd
                                                            return_repr_ts).FStar_Syntax_Syntax.pos
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____7319
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
                                             let uu____7332 =
                                               FStar_All.pipe_right ed2
                                                 FStar_Syntax_Util.get_bind_repr
                                                in
                                             FStar_All.pipe_right uu____7332
                                               FStar_Util.must
                                              in
                                           let r =
                                             let uu____7370 =
                                               FStar_Syntax_Syntax.lid_as_fv
                                                 FStar_Parser_Const.range_0
                                                 FStar_Syntax_Syntax.delta_constant
                                                 FStar_Pervasives_Native.None
                                                in
                                             FStar_All.pipe_right uu____7370
                                               FStar_Syntax_Syntax.fv_to_tm
                                              in
                                           let uu____7371 = fresh_a_and_wp ()
                                              in
                                           match uu____7371 with
                                           | (a,wp_sort_a) ->
                                               let uu____7384 =
                                                 fresh_a_and_wp ()  in
                                               (match uu____7384 with
                                                | (b,wp_sort_b) ->
                                                    let wp_sort_a_b =
                                                      let uu____7400 =
                                                        let uu____7409 =
                                                          let uu____7416 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              a
                                                             in
                                                          FStar_Syntax_Syntax.null_binder
                                                            uu____7416
                                                           in
                                                        [uu____7409]  in
                                                      let uu____7429 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          wp_sort_b
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7400 uu____7429
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
                                                      let uu____7437 =
                                                        FStar_Syntax_Syntax.bv_to_name
                                                          a
                                                         in
                                                      FStar_Syntax_Syntax.gen_bv
                                                        "x_a"
                                                        FStar_Pervasives_Native.None
                                                        uu____7437
                                                       in
                                                    let wp_g_x =
                                                      let uu____7442 =
                                                        let uu____7447 =
                                                          FStar_Syntax_Syntax.bv_to_name
                                                            wp_g
                                                           in
                                                        let uu____7448 =
                                                          let uu____7449 =
                                                            let uu____7458 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x_a
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7458
                                                              FStar_Syntax_Syntax.as_arg
                                                             in
                                                          [uu____7449]  in
                                                        FStar_Syntax_Syntax.mk_Tm_app
                                                          uu____7447
                                                          uu____7448
                                                         in
                                                      uu____7442
                                                        FStar_Pervasives_Native.None
                                                        FStar_Range.dummyRange
                                                       in
                                                    let res =
                                                      let wp =
                                                        let uu____7489 =
                                                          let uu____7494 =
                                                            let uu____7495 =
                                                              FStar_TypeChecker_Env.inst_tscheme
                                                                bind_wp
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____7495
                                                              FStar_Pervasives_Native.snd
                                                             in
                                                          let uu____7504 =
                                                            let uu____7505 =
                                                              let uu____7508
                                                                =
                                                                let uu____7511
                                                                  =
                                                                  FStar_Syntax_Syntax.bv_to_name
                                                                    a
                                                                   in
                                                                let uu____7512
                                                                  =
                                                                  let uu____7515
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                  let uu____7516
                                                                    =
                                                                    let uu____7519
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                    let uu____7520
                                                                    =
                                                                    let uu____7523
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_g  in
                                                                    [uu____7523]
                                                                     in
                                                                    uu____7519
                                                                    ::
                                                                    uu____7520
                                                                     in
                                                                  uu____7515
                                                                    ::
                                                                    uu____7516
                                                                   in
                                                                uu____7511 ::
                                                                  uu____7512
                                                                 in
                                                              r :: uu____7508
                                                               in
                                                            FStar_List.map
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____7505
                                                             in
                                                          FStar_Syntax_Syntax.mk_Tm_app
                                                            uu____7494
                                                            uu____7504
                                                           in
                                                        uu____7489
                                                          FStar_Pervasives_Native.None
                                                          FStar_Range.dummyRange
                                                         in
                                                      mk_repr b wp  in
                                                    let maybe_range_arg =
                                                      let uu____7541 =
                                                        FStar_Util.for_some
                                                          (FStar_Syntax_Util.attr_eq
                                                             FStar_Syntax_Util.dm4f_bind_range_attr)
                                                          ed2.FStar_Syntax_Syntax.eff_attrs
                                                         in
                                                      if uu____7541
                                                      then
                                                        let uu____7552 =
                                                          FStar_Syntax_Syntax.null_binder
                                                            FStar_Syntax_Syntax.t_range
                                                           in
                                                        let uu____7559 =
                                                          let uu____7568 =
                                                            FStar_Syntax_Syntax.null_binder
                                                              FStar_Syntax_Syntax.t_range
                                                             in
                                                          [uu____7568]  in
                                                        uu____7552 ::
                                                          uu____7559
                                                      else []  in
                                                    let k =
                                                      let uu____7604 =
                                                        let uu____7613 =
                                                          let uu____7622 =
                                                            FStar_Syntax_Syntax.mk_binder
                                                              a
                                                             in
                                                          let uu____7629 =
                                                            let uu____7638 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                b
                                                               in
                                                            [uu____7638]  in
                                                          uu____7622 ::
                                                            uu____7629
                                                           in
                                                        let uu____7663 =
                                                          let uu____7672 =
                                                            let uu____7681 =
                                                              FStar_Syntax_Syntax.mk_binder
                                                                wp_f
                                                               in
                                                            let uu____7688 =
                                                              let uu____7697
                                                                =
                                                                let uu____7704
                                                                  =
                                                                  let uu____7705
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    wp_f  in
                                                                  mk_repr a
                                                                    uu____7705
                                                                   in
                                                                FStar_Syntax_Syntax.null_binder
                                                                  uu____7704
                                                                 in
                                                              let uu____7706
                                                                =
                                                                let uu____7715
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    wp_g
                                                                   in
                                                                let uu____7722
                                                                  =
                                                                  let uu____7731
                                                                    =
                                                                    let uu____7738
                                                                    =
                                                                    let uu____7739
                                                                    =
                                                                    let uu____7748
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    x_a  in
                                                                    [uu____7748]
                                                                     in
                                                                    let uu____7767
                                                                    =
                                                                    let uu____7770
                                                                    =
                                                                    mk_repr b
                                                                    wp_g_x
                                                                     in
                                                                    FStar_All.pipe_left
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    uu____7770
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____7739
                                                                    uu____7767
                                                                     in
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    uu____7738
                                                                     in
                                                                  [uu____7731]
                                                                   in
                                                                uu____7715 ::
                                                                  uu____7722
                                                                 in
                                                              uu____7697 ::
                                                                uu____7706
                                                               in
                                                            uu____7681 ::
                                                              uu____7688
                                                             in
                                                          FStar_List.append
                                                            maybe_range_arg
                                                            uu____7672
                                                           in
                                                        FStar_List.append
                                                          uu____7613
                                                          uu____7663
                                                         in
                                                      let uu____7815 =
                                                        FStar_Syntax_Syntax.mk_Total
                                                          res
                                                         in
                                                      FStar_Syntax_Util.arrow
                                                        uu____7604 uu____7815
                                                       in
                                                    let uu____7818 =
                                                      FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                        env k
                                                       in
                                                    (match uu____7818 with
                                                     | (k1,uu____7826,uu____7827)
                                                         ->
                                                         let env1 =
                                                           FStar_TypeChecker_Env.set_range
                                                             env
                                                             (FStar_Pervasives_Native.snd
                                                                bind_repr_ts).FStar_Syntax_Syntax.pos
                                                            in
                                                         let env2 =
                                                           FStar_All.pipe_right
                                                             (let uu___806_7837
                                                                = env1  in
                                                              {
                                                                FStar_TypeChecker_Env.solver
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.solver);
                                                                FStar_TypeChecker_Env.range
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.range);
                                                                FStar_TypeChecker_Env.curmodule
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.curmodule);
                                                                FStar_TypeChecker_Env.gamma
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.gamma);
                                                                FStar_TypeChecker_Env.gamma_sig
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.gamma_sig);
                                                                FStar_TypeChecker_Env.gamma_cache
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.gamma_cache);
                                                                FStar_TypeChecker_Env.modules
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.modules);
                                                                FStar_TypeChecker_Env.expected_typ
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.expected_typ);
                                                                FStar_TypeChecker_Env.sigtab
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.sigtab);
                                                                FStar_TypeChecker_Env.attrtab
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.attrtab);
                                                                FStar_TypeChecker_Env.instantiate_imp
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.instantiate_imp);
                                                                FStar_TypeChecker_Env.effects
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.effects);
                                                                FStar_TypeChecker_Env.generalize
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.generalize);
                                                                FStar_TypeChecker_Env.letrecs
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.letrecs);
                                                                FStar_TypeChecker_Env.top_level
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.top_level);
                                                                FStar_TypeChecker_Env.check_uvars
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.check_uvars);
                                                                FStar_TypeChecker_Env.use_eq
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.use_eq);
                                                                FStar_TypeChecker_Env.is_iface
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.is_iface);
                                                                FStar_TypeChecker_Env.admit
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.admit);
                                                                FStar_TypeChecker_Env.lax
                                                                  = true;
                                                                FStar_TypeChecker_Env.lax_universes
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.lax_universes);
                                                                FStar_TypeChecker_Env.phase1
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.phase1);
                                                                FStar_TypeChecker_Env.failhard
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.failhard);
                                                                FStar_TypeChecker_Env.nosynth
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.nosynth);
                                                                FStar_TypeChecker_Env.uvar_subtyping
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.uvar_subtyping);
                                                                FStar_TypeChecker_Env.tc_term
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.tc_term);
                                                                FStar_TypeChecker_Env.type_of
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.type_of);
                                                                FStar_TypeChecker_Env.universe_of
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.universe_of);
                                                                FStar_TypeChecker_Env.check_type_of
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.check_type_of);
                                                                FStar_TypeChecker_Env.use_bv_sorts
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.use_bv_sorts);
                                                                FStar_TypeChecker_Env.qtbl_name_and_index
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                FStar_TypeChecker_Env.normalized_eff_names
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.normalized_eff_names);
                                                                FStar_TypeChecker_Env.fv_delta_depths
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.fv_delta_depths);
                                                                FStar_TypeChecker_Env.proof_ns
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.proof_ns);
                                                                FStar_TypeChecker_Env.synth_hook
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.synth_hook);
                                                                FStar_TypeChecker_Env.splice
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.splice);
                                                                FStar_TypeChecker_Env.mpreprocess
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.mpreprocess);
                                                                FStar_TypeChecker_Env.postprocess
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.postprocess);
                                                                FStar_TypeChecker_Env.is_native_tactic
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.is_native_tactic);
                                                                FStar_TypeChecker_Env.identifier_info
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.identifier_info);
                                                                FStar_TypeChecker_Env.tc_hooks
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.tc_hooks);
                                                                FStar_TypeChecker_Env.dsenv
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.dsenv);
                                                                FStar_TypeChecker_Env.nbe
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.nbe);
                                                                FStar_TypeChecker_Env.strict_args_tab
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.strict_args_tab);
                                                                FStar_TypeChecker_Env.erasable_types_tab
                                                                  =
                                                                  (uu___806_7837.FStar_TypeChecker_Env.erasable_types_tab)
                                                              })
                                                             (fun _7839  ->
                                                                FStar_Pervasives_Native.Some
                                                                  _7839)
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
                                              (let uu____7866 =
                                                 if
                                                   act.FStar_Syntax_Syntax.action_univs
                                                     = []
                                                 then (env, act)
                                                 else
                                                   (let uu____7880 =
                                                      FStar_Syntax_Subst.univ_var_opening
                                                        act.FStar_Syntax_Syntax.action_univs
                                                       in
                                                    match uu____7880 with
                                                    | (usubst,uvs) ->
                                                        let uu____7903 =
                                                          FStar_TypeChecker_Env.push_univ_vars
                                                            env uvs
                                                           in
                                                        let uu____7904 =
                                                          let uu___819_7905 =
                                                            act  in
                                                          let uu____7906 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          let uu____7907 =
                                                            FStar_Syntax_Subst.subst
                                                              usubst
                                                              act.FStar_Syntax_Syntax.action_typ
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.action_name
                                                              =
                                                              (uu___819_7905.FStar_Syntax_Syntax.action_name);
                                                            FStar_Syntax_Syntax.action_unqualified_name
                                                              =
                                                              (uu___819_7905.FStar_Syntax_Syntax.action_unqualified_name);
                                                            FStar_Syntax_Syntax.action_univs
                                                              = uvs;
                                                            FStar_Syntax_Syntax.action_params
                                                              =
                                                              (uu___819_7905.FStar_Syntax_Syntax.action_params);
                                                            FStar_Syntax_Syntax.action_defn
                                                              = uu____7906;
                                                            FStar_Syntax_Syntax.action_typ
                                                              = uu____7907
                                                          }  in
                                                        (uu____7903,
                                                          uu____7904))
                                                  in
                                               match uu____7866 with
                                               | (env1,act1) ->
                                                   let act_typ =
                                                     let uu____7911 =
                                                       let uu____7912 =
                                                         FStar_Syntax_Subst.compress
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                          in
                                                       uu____7912.FStar_Syntax_Syntax.n
                                                        in
                                                     match uu____7911 with
                                                     | FStar_Syntax_Syntax.Tm_arrow
                                                         (bs1,c) ->
                                                         let c1 =
                                                           FStar_Syntax_Util.comp_to_comp_typ
                                                             c
                                                            in
                                                         let uu____7938 =
                                                           FStar_Ident.lid_equals
                                                             c1.FStar_Syntax_Syntax.effect_name
                                                             ed2.FStar_Syntax_Syntax.mname
                                                            in
                                                         if uu____7938
                                                         then
                                                           let uu____7941 =
                                                             let uu____7944 =
                                                               let uu____7945
                                                                 =
                                                                 let uu____7946
                                                                   =
                                                                   FStar_List.hd
                                                                    c1.FStar_Syntax_Syntax.effect_args
                                                                    in
                                                                 FStar_Pervasives_Native.fst
                                                                   uu____7946
                                                                  in
                                                               mk_repr'
                                                                 c1.FStar_Syntax_Syntax.result_typ
                                                                 uu____7945
                                                                in
                                                             FStar_Syntax_Syntax.mk_Total
                                                               uu____7944
                                                              in
                                                           FStar_Syntax_Util.arrow
                                                             bs1 uu____7941
                                                         else
                                                           act1.FStar_Syntax_Syntax.action_typ
                                                     | uu____7969 ->
                                                         act1.FStar_Syntax_Syntax.action_typ
                                                      in
                                                   let uu____7970 =
                                                     FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                       env1 act_typ
                                                      in
                                                   (match uu____7970 with
                                                    | (act_typ1,uu____7978,g_t)
                                                        ->
                                                        let env' =
                                                          let uu___836_7981 =
                                                            FStar_TypeChecker_Env.set_expected_typ
                                                              env1 act_typ1
                                                             in
                                                          {
                                                            FStar_TypeChecker_Env.solver
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.solver);
                                                            FStar_TypeChecker_Env.range
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.range);
                                                            FStar_TypeChecker_Env.curmodule
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.curmodule);
                                                            FStar_TypeChecker_Env.gamma
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.gamma);
                                                            FStar_TypeChecker_Env.gamma_sig
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.gamma_sig);
                                                            FStar_TypeChecker_Env.gamma_cache
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.gamma_cache);
                                                            FStar_TypeChecker_Env.modules
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.modules);
                                                            FStar_TypeChecker_Env.expected_typ
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.expected_typ);
                                                            FStar_TypeChecker_Env.sigtab
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.sigtab);
                                                            FStar_TypeChecker_Env.attrtab
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.attrtab);
                                                            FStar_TypeChecker_Env.instantiate_imp
                                                              = false;
                                                            FStar_TypeChecker_Env.effects
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.effects);
                                                            FStar_TypeChecker_Env.generalize
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.generalize);
                                                            FStar_TypeChecker_Env.letrecs
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.letrecs);
                                                            FStar_TypeChecker_Env.top_level
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.top_level);
                                                            FStar_TypeChecker_Env.check_uvars
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.check_uvars);
                                                            FStar_TypeChecker_Env.use_eq
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.use_eq);
                                                            FStar_TypeChecker_Env.is_iface
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.is_iface);
                                                            FStar_TypeChecker_Env.admit
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.admit);
                                                            FStar_TypeChecker_Env.lax
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.lax);
                                                            FStar_TypeChecker_Env.lax_universes
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.lax_universes);
                                                            FStar_TypeChecker_Env.phase1
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.phase1);
                                                            FStar_TypeChecker_Env.failhard
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.failhard);
                                                            FStar_TypeChecker_Env.nosynth
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.nosynth);
                                                            FStar_TypeChecker_Env.uvar_subtyping
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.uvar_subtyping);
                                                            FStar_TypeChecker_Env.tc_term
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.tc_term);
                                                            FStar_TypeChecker_Env.type_of
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.type_of);
                                                            FStar_TypeChecker_Env.universe_of
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.universe_of);
                                                            FStar_TypeChecker_Env.check_type_of
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.check_type_of);
                                                            FStar_TypeChecker_Env.use_bv_sorts
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.use_bv_sorts);
                                                            FStar_TypeChecker_Env.qtbl_name_and_index
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                            FStar_TypeChecker_Env.normalized_eff_names
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.normalized_eff_names);
                                                            FStar_TypeChecker_Env.fv_delta_depths
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.fv_delta_depths);
                                                            FStar_TypeChecker_Env.proof_ns
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.proof_ns);
                                                            FStar_TypeChecker_Env.synth_hook
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.synth_hook);
                                                            FStar_TypeChecker_Env.splice
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.splice);
                                                            FStar_TypeChecker_Env.mpreprocess
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.mpreprocess);
                                                            FStar_TypeChecker_Env.postprocess
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.postprocess);
                                                            FStar_TypeChecker_Env.is_native_tactic
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.is_native_tactic);
                                                            FStar_TypeChecker_Env.identifier_info
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.identifier_info);
                                                            FStar_TypeChecker_Env.tc_hooks
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.tc_hooks);
                                                            FStar_TypeChecker_Env.dsenv
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.dsenv);
                                                            FStar_TypeChecker_Env.nbe
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.nbe);
                                                            FStar_TypeChecker_Env.strict_args_tab
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.strict_args_tab);
                                                            FStar_TypeChecker_Env.erasable_types_tab
                                                              =
                                                              (uu___836_7981.FStar_TypeChecker_Env.erasable_types_tab)
                                                          }  in
                                                        ((let uu____7984 =
                                                            FStar_TypeChecker_Env.debug
                                                              env1
                                                              (FStar_Options.Other
                                                                 "ED")
                                                             in
                                                          if uu____7984
                                                          then
                                                            let uu____7988 =
                                                              FStar_Ident.text_of_lid
                                                                act1.FStar_Syntax_Syntax.action_name
                                                               in
                                                            let uu____7990 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act1.FStar_Syntax_Syntax.action_defn
                                                               in
                                                            let uu____7992 =
                                                              FStar_Syntax_Print.term_to_string
                                                                act_typ1
                                                               in
                                                            FStar_Util.print3
                                                              "Checking action %s:\n[definition]: %s\n[cps'd type]: %s\n"
                                                              uu____7988
                                                              uu____7990
                                                              uu____7992
                                                          else ());
                                                         (let uu____7997 =
                                                            FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                              env'
                                                              act1.FStar_Syntax_Syntax.action_defn
                                                             in
                                                          match uu____7997
                                                          with
                                                          | (act_defn,uu____8005,g_a)
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
                                                              let uu____8009
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
                                                                    let uu____8045
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8045
                                                                    with
                                                                    | 
                                                                    (bs2,uu____8057)
                                                                    ->
                                                                    let res =
                                                                    mk_repr'
                                                                    FStar_Syntax_Syntax.tun
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    let k =
                                                                    let uu____8064
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    res  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8064
                                                                     in
                                                                    let uu____8067
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                                                    env1 k
                                                                     in
                                                                    (match uu____8067
                                                                    with
                                                                    | 
                                                                    (k1,uu____8081,g)
                                                                    ->
                                                                    (k1, g)))
                                                                | uu____8085
                                                                    ->
                                                                    let uu____8086
                                                                    =
                                                                    let uu____8092
                                                                    =
                                                                    let uu____8094
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    act_typ3
                                                                     in
                                                                    let uu____8096
                                                                    =
                                                                    FStar_Syntax_Print.tag_of_term
                                                                    act_typ3
                                                                     in
                                                                    FStar_Util.format2
                                                                    "Actions must have function types (not: %s, a.k.a. %s)"
                                                                    uu____8094
                                                                    uu____8096
                                                                     in
                                                                    (FStar_Errors.Fatal_ActionMustHaveFunctionType,
                                                                    uu____8092)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____8086
                                                                    act_defn1.FStar_Syntax_Syntax.pos
                                                                 in
                                                              (match uu____8009
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
                                                                    let uu____8114
                                                                    =
                                                                    let uu____8115
                                                                    =
                                                                    let uu____8116
                                                                    =
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_t g  in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_k
                                                                    uu____8116
                                                                     in
                                                                    FStar_TypeChecker_Env.conj_guard
                                                                    g_a
                                                                    uu____8115
                                                                     in
                                                                    FStar_TypeChecker_Rel.force_trivial_guard
                                                                    env1
                                                                    uu____8114);
                                                                    (
                                                                    let act_typ3
                                                                    =
                                                                    let uu____8118
                                                                    =
                                                                    let uu____8119
                                                                    =
                                                                    FStar_Syntax_Subst.compress
                                                                    expected_k
                                                                     in
                                                                    uu____8119.FStar_Syntax_Syntax.n
                                                                     in
                                                                    match uu____8118
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_arrow
                                                                    (bs1,c)
                                                                    ->
                                                                    let uu____8144
                                                                    =
                                                                    FStar_Syntax_Subst.open_comp
                                                                    bs1 c  in
                                                                    (match uu____8144
                                                                    with
                                                                    | 
                                                                    (bs2,c1)
                                                                    ->
                                                                    let uu____8151
                                                                    =
                                                                    destruct_repr
                                                                    (FStar_Syntax_Util.comp_result
                                                                    c1)  in
                                                                    (match uu____8151
                                                                    with
                                                                    | 
                                                                    (a,wp) ->
                                                                    let c2 =
                                                                    let uu____8171
                                                                    =
                                                                    let uu____8172
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 a
                                                                     in
                                                                    [uu____8172]
                                                                     in
                                                                    let uu____8173
                                                                    =
                                                                    let uu____8184
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    wp  in
                                                                    [uu____8184]
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____8171;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    =
                                                                    (ed2.FStar_Syntax_Syntax.mname);
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    = a;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____8173;
                                                                    FStar_Syntax_Syntax.flags
                                                                    = []
                                                                    }  in
                                                                    let uu____8209
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Comp
                                                                    c2  in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs2
                                                                    uu____8209))
                                                                    | 
                                                                    uu____8212
                                                                    ->
                                                                    failwith
                                                                    "Impossible (expected_k is an arrow)"
                                                                     in
                                                                    let uu____8214
                                                                    =
                                                                    if
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    = []
                                                                    then
                                                                    FStar_TypeChecker_Util.generalize_universes
                                                                    env1
                                                                    act_defn1
                                                                    else
                                                                    (let uu____8236
                                                                    =
                                                                    FStar_Syntax_Subst.close_univ_vars
                                                                    act1.FStar_Syntax_Syntax.action_univs
                                                                    act_defn1
                                                                     in
                                                                    ((act1.FStar_Syntax_Syntax.action_univs),
                                                                    uu____8236))
                                                                     in
                                                                    match uu____8214
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
                                                                    let uu___886_8255
                                                                    = act1
                                                                     in
                                                                    {
                                                                    FStar_Syntax_Syntax.action_name
                                                                    =
                                                                    (uu___886_8255.FStar_Syntax_Syntax.action_name);
                                                                    FStar_Syntax_Syntax.action_unqualified_name
                                                                    =
                                                                    (uu___886_8255.FStar_Syntax_Syntax.action_unqualified_name);
                                                                    FStar_Syntax_Syntax.action_univs
                                                                    = univs1;
                                                                    FStar_Syntax_Syntax.action_params
                                                                    =
                                                                    (uu___886_8255.FStar_Syntax_Syntax.action_params);
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
                                match uu____6693 with
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
                                      let uu____8298 =
                                        FStar_Syntax_Subst.shift_subst
                                          (FStar_List.length ed_bs)
                                          ed_univs_closing
                                         in
                                      FStar_Syntax_Subst.subst_tscheme
                                        uu____8298 ts1
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
                                          uu____8310 ->
                                          FStar_Syntax_Syntax.Primitive_eff
                                            combinators1
                                      | FStar_Syntax_Syntax.DM4F_eff
                                          uu____8311 ->
                                          FStar_Syntax_Syntax.DM4F_eff
                                            combinators1
                                      | uu____8312 ->
                                          failwith
                                            "Impossible! tc_eff_decl on a layered effect is not expected"
                                       in
                                    let ed3 =
                                      let uu___906_8315 = ed2  in
                                      let uu____8316 = cl signature  in
                                      let uu____8317 =
                                        FStar_List.map
                                          (fun a  ->
                                             let uu___909_8325 = a  in
                                             let uu____8326 =
                                               let uu____8327 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_defn))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8327
                                                 FStar_Pervasives_Native.snd
                                                in
                                             let uu____8352 =
                                               let uu____8353 =
                                                 cl
                                                   ((a.FStar_Syntax_Syntax.action_univs),
                                                     (a.FStar_Syntax_Syntax.action_typ))
                                                  in
                                               FStar_All.pipe_right
                                                 uu____8353
                                                 FStar_Pervasives_Native.snd
                                                in
                                             {
                                               FStar_Syntax_Syntax.action_name
                                                 =
                                                 (uu___909_8325.FStar_Syntax_Syntax.action_name);
                                               FStar_Syntax_Syntax.action_unqualified_name
                                                 =
                                                 (uu___909_8325.FStar_Syntax_Syntax.action_unqualified_name);
                                               FStar_Syntax_Syntax.action_univs
                                                 =
                                                 (uu___909_8325.FStar_Syntax_Syntax.action_univs);
                                               FStar_Syntax_Syntax.action_params
                                                 =
                                                 (uu___909_8325.FStar_Syntax_Syntax.action_params);
                                               FStar_Syntax_Syntax.action_defn
                                                 = uu____8326;
                                               FStar_Syntax_Syntax.action_typ
                                                 = uu____8352
                                             }) actions
                                         in
                                      {
                                        FStar_Syntax_Syntax.mname =
                                          (uu___906_8315.FStar_Syntax_Syntax.mname);
                                        FStar_Syntax_Syntax.cattributes =
                                          (uu___906_8315.FStar_Syntax_Syntax.cattributes);
                                        FStar_Syntax_Syntax.univs =
                                          (uu___906_8315.FStar_Syntax_Syntax.univs);
                                        FStar_Syntax_Syntax.binders =
                                          (uu___906_8315.FStar_Syntax_Syntax.binders);
                                        FStar_Syntax_Syntax.signature =
                                          uu____8316;
                                        FStar_Syntax_Syntax.combinators =
                                          combinators2;
                                        FStar_Syntax_Syntax.actions =
                                          uu____8317;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          (uu___906_8315.FStar_Syntax_Syntax.eff_attrs)
                                      }  in
                                    ((let uu____8379 =
                                        FStar_All.pipe_left
                                          (FStar_TypeChecker_Env.debug env)
                                          (FStar_Options.Other "ED")
                                         in
                                      if uu____8379
                                      then
                                        let uu____8384 =
                                          FStar_Syntax_Print.eff_decl_to_string
                                            false ed3
                                           in
                                        FStar_Util.print1
                                          "Typechecked effect declaration:\n\t%s\n"
                                          uu____8384
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
        let uu____8410 =
          let uu____8425 =
            FStar_All.pipe_right ed FStar_Syntax_Util.is_layered  in
          if uu____8425 then tc_layered_eff_decl else tc_non_layered_eff_decl
           in
        uu____8410 env ed quals
  
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
        let fail1 uu____8475 =
          let uu____8476 =
            FStar_TypeChecker_Err.unexpected_signature_for_monad env m s  in
          let uu____8482 = FStar_Ident.range_of_lid m  in
          FStar_Errors.raise_error uu____8476 uu____8482  in
        let s1 = FStar_Syntax_Subst.compress s  in
        match s1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let bs1 = FStar_Syntax_Subst.open_binders bs  in
            (match bs1 with
             | (a,uu____8526)::(wp,uu____8528)::[] ->
                 (a, (wp.FStar_Syntax_Syntax.sort))
             | uu____8557 -> fail1 ())
        | uu____8558 -> fail1 ()
  
let (tc_layered_lift :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.sub_eff -> FStar_Syntax_Syntax.sub_eff)
  =
  fun env0  ->
    fun sub1  ->
      (let uu____8571 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
           (FStar_Options.Other "LayeredEffects")
          in
       if uu____8571
       then
         let uu____8576 = FStar_Syntax_Print.sub_eff_to_string sub1  in
         FStar_Util.print1 "Typechecking sub_effect: %s\n" uu____8576
       else ());
      (let lift_ts =
         FStar_All.pipe_right sub1.FStar_Syntax_Syntax.lift FStar_Util.must
          in
       let r =
         let uu____8593 =
           FStar_All.pipe_right lift_ts FStar_Pervasives_Native.snd  in
         uu____8593.FStar_Syntax_Syntax.pos  in
       (let src_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.source
           in
        let tgt_ed =
          FStar_TypeChecker_Env.get_effect_decl env0
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____8605 =
          ((FStar_All.pipe_right src_ed FStar_Syntax_Util.is_layered) &&
             (let uu____8609 =
                let uu____8610 =
                  FStar_All.pipe_right src_ed
                    FStar_Syntax_Util.get_layered_effect_base
                   in
                FStar_All.pipe_right uu____8610 FStar_Util.must  in
              FStar_Ident.lid_equals uu____8609
                tgt_ed.FStar_Syntax_Syntax.mname))
            ||
            (((FStar_All.pipe_right tgt_ed FStar_Syntax_Util.is_layered) &&
                (let uu____8619 =
                   let uu____8620 =
                     FStar_All.pipe_right tgt_ed
                       FStar_Syntax_Util.get_layered_effect_base
                      in
                   FStar_All.pipe_right uu____8620 FStar_Util.must  in
                 FStar_Ident.lid_equals uu____8619
                   src_ed.FStar_Syntax_Syntax.mname))
               &&
               (let uu____8628 =
                  FStar_Ident.lid_equals src_ed.FStar_Syntax_Syntax.mname
                    FStar_Parser_Const.effect_PURE_lid
                   in
                Prims.op_Negation uu____8628))
           in
        if uu____8605
        then
          let uu____8631 =
            let uu____8637 =
              let uu____8639 =
                FStar_All.pipe_right src_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              let uu____8642 =
                FStar_All.pipe_right tgt_ed.FStar_Syntax_Syntax.mname
                  FStar_Ident.string_of_lid
                 in
              FStar_Util.format2
                "Lifts cannot be defined from a layered effect to its repr or vice versa (%s and %s here)"
                uu____8639 uu____8642
               in
            (FStar_Errors.Fatal_EffectsCannotBeComposed, uu____8637)  in
          FStar_Errors.raise_error uu____8631 r
        else ());
       (let uu____8649 = check_and_gen env0 "" "lift" Prims.int_one lift_ts
           in
        match uu____8649 with
        | (us,lift,lift_ty) ->
            ((let uu____8663 =
                FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0)
                  (FStar_Options.Other "LayeredEffects")
                 in
              if uu____8663
              then
                let uu____8668 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift)  in
                let uu____8674 =
                  FStar_Syntax_Print.tscheme_to_string (us, lift_ty)  in
                FStar_Util.print2 "Typechecked lift: %s and lift_ty: %s\n"
                  uu____8668 uu____8674
              else ());
             (let uu____8683 = FStar_Syntax_Subst.open_univ_vars us lift_ty
                 in
              match uu____8683 with
              | (us1,lift_ty1) ->
                  let env = FStar_TypeChecker_Env.push_univ_vars env0 us1  in
                  let lift_t_shape_error s =
                    let uu____8700 =
                      FStar_Ident.string_of_lid
                        sub1.FStar_Syntax_Syntax.source
                       in
                    let uu____8702 =
                      FStar_Ident.string_of_lid
                        sub1.FStar_Syntax_Syntax.target
                       in
                    let uu____8704 =
                      FStar_Syntax_Print.term_to_string lift_ty1  in
                    FStar_Util.format4
                      "Unexpected shape of lift %s~>%s, reason:%s (t:%s)"
                      uu____8700 uu____8702 s uu____8704
                     in
                  let uu____8707 =
                    let uu____8714 =
                      let uu____8719 = FStar_Syntax_Util.type_u ()  in
                      FStar_All.pipe_right uu____8719
                        (fun uu____8736  ->
                           match uu____8736 with
                           | (t,u) ->
                               let uu____8747 =
                                 let uu____8748 =
                                   FStar_Syntax_Syntax.gen_bv "a"
                                     FStar_Pervasives_Native.None t
                                    in
                                 FStar_All.pipe_right uu____8748
                                   FStar_Syntax_Syntax.mk_binder
                                  in
                               (uu____8747, u))
                       in
                    match uu____8714 with
                    | (a,u_a) ->
                        let rest_bs =
                          let uu____8767 =
                            let uu____8768 =
                              FStar_Syntax_Subst.compress lift_ty1  in
                            uu____8768.FStar_Syntax_Syntax.n  in
                          match uu____8767 with
                          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____8780) when
                              (FStar_List.length bs) >= (Prims.of_int (2)) ->
                              let uu____8808 =
                                FStar_Syntax_Subst.open_binders bs  in
                              (match uu____8808 with
                               | (a',uu____8818)::bs1 ->
                                   let uu____8838 =
                                     let uu____8839 =
                                       FStar_All.pipe_right bs1
                                         (FStar_List.splitAt
                                            ((FStar_List.length bs1) -
                                               Prims.int_one))
                                        in
                                     FStar_All.pipe_right uu____8839
                                       FStar_Pervasives_Native.fst
                                      in
                                   let uu____8905 =
                                     let uu____8918 =
                                       let uu____8921 =
                                         let uu____8922 =
                                           let uu____8929 =
                                             FStar_Syntax_Syntax.bv_to_name
                                               (FStar_Pervasives_Native.fst a)
                                              in
                                           (a', uu____8929)  in
                                         FStar_Syntax_Syntax.NT uu____8922
                                          in
                                       [uu____8921]  in
                                     FStar_Syntax_Subst.subst_binders
                                       uu____8918
                                      in
                                   FStar_All.pipe_right uu____8838 uu____8905)
                          | uu____8944 ->
                              let uu____8945 =
                                let uu____8951 =
                                  lift_t_shape_error
                                    "either not an arrow, or not enough binders"
                                   in
                                (FStar_Errors.Fatal_UnexpectedExpressionType,
                                  uu____8951)
                                 in
                              FStar_Errors.raise_error uu____8945 r
                           in
                        let uu____8963 =
                          let uu____8974 =
                            let uu____8979 =
                              FStar_TypeChecker_Env.push_binders env (a ::
                                rest_bs)
                               in
                            let uu____8986 =
                              let uu____8987 =
                                FStar_All.pipe_right a
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_All.pipe_right uu____8987
                                FStar_Syntax_Syntax.bv_to_name
                               in
                            FStar_TypeChecker_Util.fresh_effect_repr_en
                              uu____8979 r sub1.FStar_Syntax_Syntax.source
                              u_a uu____8986
                             in
                          match uu____8974 with
                          | (f_sort,g) ->
                              let uu____9008 =
                                let uu____9015 =
                                  FStar_Syntax_Syntax.gen_bv "f"
                                    FStar_Pervasives_Native.None f_sort
                                   in
                                FStar_All.pipe_right uu____9015
                                  FStar_Syntax_Syntax.mk_binder
                                 in
                              (uu____9008, g)
                           in
                        (match uu____8963 with
                         | (f_b,g_f_b) ->
                             let bs = a :: (FStar_List.append rest_bs [f_b])
                                in
                             let uu____9082 =
                               let uu____9087 =
                                 FStar_TypeChecker_Env.push_binders env bs
                                  in
                               let uu____9088 =
                                 let uu____9089 =
                                   FStar_All.pipe_right a
                                     FStar_Pervasives_Native.fst
                                    in
                                 FStar_All.pipe_right uu____9089
                                   FStar_Syntax_Syntax.bv_to_name
                                  in
                               FStar_TypeChecker_Util.fresh_effect_repr_en
                                 uu____9087 r sub1.FStar_Syntax_Syntax.target
                                 u_a uu____9088
                                in
                             (match uu____9082 with
                              | (repr,g_repr) ->
                                  let uu____9106 =
                                    let uu____9111 =
                                      FStar_TypeChecker_Env.push_binders env
                                        bs
                                       in
                                    let uu____9112 =
                                      let uu____9114 =
                                        FStar_Ident.string_of_lid
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      let uu____9116 =
                                        FStar_Ident.string_of_lid
                                          sub1.FStar_Syntax_Syntax.target
                                         in
                                      FStar_Util.format2
                                        "implicit for pure_wp in typechecking lift %s~>%s"
                                        uu____9114 uu____9116
                                       in
                                    pure_wp_uvar uu____9111 repr uu____9112 r
                                     in
                                  (match uu____9106 with
                                   | (pure_wp_uvar1,guard_wp) ->
                                       let c =
                                         let uu____9128 =
                                           let uu____9129 =
                                             let uu____9130 =
                                               FStar_TypeChecker_Env.new_u_univ
                                                 ()
                                                in
                                             [uu____9130]  in
                                           let uu____9131 =
                                             let uu____9142 =
                                               FStar_All.pipe_right
                                                 pure_wp_uvar1
                                                 FStar_Syntax_Syntax.as_arg
                                                in
                                             [uu____9142]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____9129;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               FStar_Parser_Const.effect_PURE_lid;
                                             FStar_Syntax_Syntax.result_typ =
                                               repr;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____9131;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____9128
                                          in
                                       let uu____9175 =
                                         FStar_Syntax_Util.arrow bs c  in
                                       let uu____9178 =
                                         let uu____9179 =
                                           FStar_TypeChecker_Env.conj_guard
                                             g_f_b g_repr
                                            in
                                         FStar_TypeChecker_Env.conj_guard
                                           uu____9179 guard_wp
                                          in
                                       (uu____9175, uu____9178))))
                     in
                  (match uu____8707 with
                   | (k,g_k) ->
                       ((let uu____9189 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug env)
                             (FStar_Options.Other "LayeredEffects")
                            in
                         if uu____9189
                         then
                           let uu____9194 =
                             FStar_Syntax_Print.term_to_string k  in
                           FStar_Util.print1
                             "tc_layered_lift: before unification k: %s\n"
                             uu____9194
                         else ());
                        (let g = FStar_TypeChecker_Rel.teq env lift_ty1 k  in
                         FStar_TypeChecker_Rel.force_trivial_guard env g_k;
                         FStar_TypeChecker_Rel.force_trivial_guard env g;
                         (let uu____9203 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug env0)
                              (FStar_Options.Other "LayeredEffects")
                             in
                          if uu____9203
                          then
                            let uu____9208 =
                              FStar_Syntax_Print.term_to_string k  in
                            FStar_Util.print1 "After unification k: %s\n"
                              uu____9208
                          else ());
                         (let k1 =
                            FStar_All.pipe_right k
                              (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                 env)
                             in
                          check_no_subtyping_for_layered_combinator env k1
                            FStar_Pervasives_Native.None;
                          (let sub2 =
                             let uu___1003_9216 = sub1  in
                             let uu____9217 =
                               let uu____9220 =
                                 let uu____9221 =
                                   FStar_Syntax_Subst.close_univ_vars us1 k1
                                    in
                                 (us1, uu____9221)  in
                               FStar_Pervasives_Native.Some uu____9220  in
                             {
                               FStar_Syntax_Syntax.source =
                                 (uu___1003_9216.FStar_Syntax_Syntax.source);
                               FStar_Syntax_Syntax.target =
                                 (uu___1003_9216.FStar_Syntax_Syntax.target);
                               FStar_Syntax_Syntax.lift_wp = uu____9217;
                               FStar_Syntax_Syntax.lift =
                                 (FStar_Pervasives_Native.Some (us1, lift))
                             }  in
                           (let uu____9233 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env0)
                                (FStar_Options.Other "LayeredEffects")
                               in
                            if uu____9233
                            then
                              let uu____9238 =
                                FStar_Syntax_Print.sub_eff_to_string sub2  in
                              FStar_Util.print1 "Final sub_effect: %s\n"
                                uu____9238
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
          let uu____9275 =
            FStar_TypeChecker_TcTerm.tc_check_trivial_guard env1 t k  in
          FStar_TypeChecker_Util.generalize_universes env1 uu____9275  in
        let ed_src =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.source
           in
        let ed_tgt =
          FStar_TypeChecker_Env.get_effect_decl env
            sub1.FStar_Syntax_Syntax.target
           in
        let uu____9278 =
          (FStar_All.pipe_right ed_src FStar_Syntax_Util.is_layered) ||
            (FStar_All.pipe_right ed_tgt FStar_Syntax_Util.is_layered)
           in
        if uu____9278
        then tc_layered_lift env sub1
        else
          (let uu____9285 =
             let uu____9292 =
               FStar_TypeChecker_Env.lookup_effect_lid env
                 sub1.FStar_Syntax_Syntax.source
                in
             monad_signature env sub1.FStar_Syntax_Syntax.source uu____9292
              in
           match uu____9285 with
           | (a,wp_a_src) ->
               let uu____9299 =
                 let uu____9306 =
                   FStar_TypeChecker_Env.lookup_effect_lid env
                     sub1.FStar_Syntax_Syntax.target
                    in
                 monad_signature env sub1.FStar_Syntax_Syntax.target
                   uu____9306
                  in
               (match uu____9299 with
                | (b,wp_b_tgt) ->
                    let wp_a_tgt =
                      let uu____9314 =
                        let uu____9317 =
                          let uu____9318 =
                            let uu____9325 = FStar_Syntax_Syntax.bv_to_name a
                               in
                            (b, uu____9325)  in
                          FStar_Syntax_Syntax.NT uu____9318  in
                        [uu____9317]  in
                      FStar_Syntax_Subst.subst uu____9314 wp_b_tgt  in
                    let expected_k =
                      let uu____9333 =
                        let uu____9342 = FStar_Syntax_Syntax.mk_binder a  in
                        let uu____9349 =
                          let uu____9358 =
                            FStar_Syntax_Syntax.null_binder wp_a_src  in
                          [uu____9358]  in
                        uu____9342 :: uu____9349  in
                      let uu____9383 = FStar_Syntax_Syntax.mk_Total wp_a_tgt
                         in
                      FStar_Syntax_Util.arrow uu____9333 uu____9383  in
                    let repr_type eff_name a1 wp =
                      (let uu____9405 =
                         let uu____9407 =
                           FStar_TypeChecker_Env.is_reifiable_effect env
                             eff_name
                            in
                         Prims.op_Negation uu____9407  in
                       if uu____9405
                       then
                         let uu____9410 =
                           let uu____9416 =
                             FStar_Util.format1 "Effect %s cannot be reified"
                               eff_name.FStar_Ident.str
                              in
                           (FStar_Errors.Fatal_EffectCannotBeReified,
                             uu____9416)
                            in
                         let uu____9420 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error uu____9410 uu____9420
                       else ());
                      (let uu____9423 =
                         FStar_TypeChecker_Env.effect_decl_opt env eff_name
                          in
                       match uu____9423 with
                       | FStar_Pervasives_Native.None  ->
                           failwith
                             "internal error: reifiable effect has no decl?"
                       | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                           let repr =
                             let uu____9456 =
                               let uu____9457 =
                                 FStar_All.pipe_right ed
                                   FStar_Syntax_Util.get_eff_repr
                                  in
                               FStar_All.pipe_right uu____9457
                                 FStar_Util.must
                                in
                             FStar_TypeChecker_Env.inst_effect_fun_with
                               [FStar_Syntax_Syntax.U_unknown] env ed
                               uu____9456
                              in
                           let uu____9464 =
                             FStar_TypeChecker_Env.get_range env  in
                           let uu____9465 =
                             let uu____9472 =
                               let uu____9473 =
                                 let uu____9490 =
                                   let uu____9501 =
                                     FStar_Syntax_Syntax.as_arg a1  in
                                   let uu____9510 =
                                     let uu____9521 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____9521]  in
                                   uu____9501 :: uu____9510  in
                                 (repr, uu____9490)  in
                               FStar_Syntax_Syntax.Tm_app uu____9473  in
                             FStar_Syntax_Syntax.mk uu____9472  in
                           uu____9465 FStar_Pervasives_Native.None uu____9464)
                       in
                    let uu____9566 =
                      match ((sub1.FStar_Syntax_Syntax.lift),
                              (sub1.FStar_Syntax_Syntax.lift_wp))
                      with
                      | (FStar_Pervasives_Native.None
                         ,FStar_Pervasives_Native.None ) ->
                          failwith "Impossible (parser)"
                      | (lift,FStar_Pervasives_Native.Some (uvs,lift_wp)) ->
                          let uu____9739 =
                            if (FStar_List.length uvs) > Prims.int_zero
                            then
                              let uu____9750 =
                                FStar_Syntax_Subst.univ_var_opening uvs  in
                              match uu____9750 with
                              | (usubst,uvs1) ->
                                  let uu____9773 =
                                    FStar_TypeChecker_Env.push_univ_vars env
                                      uvs1
                                     in
                                  let uu____9774 =
                                    FStar_Syntax_Subst.subst usubst lift_wp
                                     in
                                  (uu____9773, uu____9774)
                            else (env, lift_wp)  in
                          (match uu____9739 with
                           | (env1,lift_wp1) ->
                               let lift_wp2 =
                                 if (FStar_List.length uvs) = Prims.int_zero
                                 then check_and_gen1 env1 lift_wp1 expected_k
                                 else
                                   (let lift_wp2 =
                                      FStar_TypeChecker_TcTerm.tc_check_trivial_guard
                                        env1 lift_wp1 expected_k
                                       in
                                    let uu____9824 =
                                      FStar_Syntax_Subst.close_univ_vars uvs
                                        lift_wp2
                                       in
                                    (uvs, uu____9824))
                                  in
                               (lift, lift_wp2))
                      | (FStar_Pervasives_Native.Some
                         (what,lift),FStar_Pervasives_Native.None ) ->
                          let uu____9895 =
                            if (FStar_List.length what) > Prims.int_zero
                            then
                              let uu____9910 =
                                FStar_Syntax_Subst.univ_var_opening what  in
                              match uu____9910 with
                              | (usubst,uvs) ->
                                  let uu____9935 =
                                    FStar_Syntax_Subst.subst usubst lift  in
                                  (uvs, uu____9935)
                            else ([], lift)  in
                          (match uu____9895 with
                           | (uvs,lift1) ->
                               ((let uu____9971 =
                                   FStar_TypeChecker_Env.debug env
                                     (FStar_Options.Other "ED")
                                    in
                                 if uu____9971
                                 then
                                   let uu____9975 =
                                     FStar_Syntax_Print.term_to_string lift1
                                      in
                                   FStar_Util.print1 "Lift for free : %s\n"
                                     uu____9975
                                 else ());
                                (let dmff_env =
                                   FStar_TypeChecker_DMFF.empty env
                                     (FStar_TypeChecker_TcTerm.tc_constant
                                        env FStar_Range.dummyRange)
                                    in
                                 let uu____9981 =
                                   let uu____9988 =
                                     FStar_TypeChecker_Env.push_univ_vars env
                                       uvs
                                      in
                                   FStar_TypeChecker_TcTerm.tc_term
                                     uu____9988 lift1
                                    in
                                 match uu____9981 with
                                 | (lift2,comp,uu____10013) ->
                                     let uu____10014 =
                                       FStar_TypeChecker_DMFF.star_expr
                                         dmff_env lift2
                                        in
                                     (match uu____10014 with
                                      | (uu____10043,lift_wp,lift_elab) ->
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
                                            let uu____10075 =
                                              let uu____10086 =
                                                FStar_TypeChecker_Util.generalize_universes
                                                  env lift_elab1
                                                 in
                                              FStar_Pervasives_Native.Some
                                                uu____10086
                                               in
                                            let uu____10103 =
                                              FStar_TypeChecker_Util.generalize_universes
                                                env lift_wp1
                                               in
                                            (uu____10075, uu____10103)
                                          else
                                            (let uu____10132 =
                                               let uu____10143 =
                                                 let uu____10152 =
                                                   FStar_Syntax_Subst.close_univ_vars
                                                     uvs lift_elab1
                                                    in
                                                 (uvs, uu____10152)  in
                                               FStar_Pervasives_Native.Some
                                                 uu____10143
                                                in
                                             let uu____10167 =
                                               let uu____10176 =
                                                 FStar_Syntax_Subst.close_univ_vars
                                                   uvs lift_wp1
                                                  in
                                               (uvs, uu____10176)  in
                                             (uu____10132, uu____10167))))))
                       in
                    (match uu____9566 with
                     | (lift,lift_wp) ->
                         let env1 =
                           let uu___1087_10240 = env  in
                           {
                             FStar_TypeChecker_Env.solver =
                               (uu___1087_10240.FStar_TypeChecker_Env.solver);
                             FStar_TypeChecker_Env.range =
                               (uu___1087_10240.FStar_TypeChecker_Env.range);
                             FStar_TypeChecker_Env.curmodule =
                               (uu___1087_10240.FStar_TypeChecker_Env.curmodule);
                             FStar_TypeChecker_Env.gamma =
                               (uu___1087_10240.FStar_TypeChecker_Env.gamma);
                             FStar_TypeChecker_Env.gamma_sig =
                               (uu___1087_10240.FStar_TypeChecker_Env.gamma_sig);
                             FStar_TypeChecker_Env.gamma_cache =
                               (uu___1087_10240.FStar_TypeChecker_Env.gamma_cache);
                             FStar_TypeChecker_Env.modules =
                               (uu___1087_10240.FStar_TypeChecker_Env.modules);
                             FStar_TypeChecker_Env.expected_typ =
                               (uu___1087_10240.FStar_TypeChecker_Env.expected_typ);
                             FStar_TypeChecker_Env.sigtab =
                               (uu___1087_10240.FStar_TypeChecker_Env.sigtab);
                             FStar_TypeChecker_Env.attrtab =
                               (uu___1087_10240.FStar_TypeChecker_Env.attrtab);
                             FStar_TypeChecker_Env.instantiate_imp =
                               (uu___1087_10240.FStar_TypeChecker_Env.instantiate_imp);
                             FStar_TypeChecker_Env.effects =
                               (uu___1087_10240.FStar_TypeChecker_Env.effects);
                             FStar_TypeChecker_Env.generalize =
                               (uu___1087_10240.FStar_TypeChecker_Env.generalize);
                             FStar_TypeChecker_Env.letrecs =
                               (uu___1087_10240.FStar_TypeChecker_Env.letrecs);
                             FStar_TypeChecker_Env.top_level =
                               (uu___1087_10240.FStar_TypeChecker_Env.top_level);
                             FStar_TypeChecker_Env.check_uvars =
                               (uu___1087_10240.FStar_TypeChecker_Env.check_uvars);
                             FStar_TypeChecker_Env.use_eq =
                               (uu___1087_10240.FStar_TypeChecker_Env.use_eq);
                             FStar_TypeChecker_Env.is_iface =
                               (uu___1087_10240.FStar_TypeChecker_Env.is_iface);
                             FStar_TypeChecker_Env.admit =
                               (uu___1087_10240.FStar_TypeChecker_Env.admit);
                             FStar_TypeChecker_Env.lax = true;
                             FStar_TypeChecker_Env.lax_universes =
                               (uu___1087_10240.FStar_TypeChecker_Env.lax_universes);
                             FStar_TypeChecker_Env.phase1 =
                               (uu___1087_10240.FStar_TypeChecker_Env.phase1);
                             FStar_TypeChecker_Env.failhard =
                               (uu___1087_10240.FStar_TypeChecker_Env.failhard);
                             FStar_TypeChecker_Env.nosynth =
                               (uu___1087_10240.FStar_TypeChecker_Env.nosynth);
                             FStar_TypeChecker_Env.uvar_subtyping =
                               (uu___1087_10240.FStar_TypeChecker_Env.uvar_subtyping);
                             FStar_TypeChecker_Env.tc_term =
                               (uu___1087_10240.FStar_TypeChecker_Env.tc_term);
                             FStar_TypeChecker_Env.type_of =
                               (uu___1087_10240.FStar_TypeChecker_Env.type_of);
                             FStar_TypeChecker_Env.universe_of =
                               (uu___1087_10240.FStar_TypeChecker_Env.universe_of);
                             FStar_TypeChecker_Env.check_type_of =
                               (uu___1087_10240.FStar_TypeChecker_Env.check_type_of);
                             FStar_TypeChecker_Env.use_bv_sorts =
                               (uu___1087_10240.FStar_TypeChecker_Env.use_bv_sorts);
                             FStar_TypeChecker_Env.qtbl_name_and_index =
                               (uu___1087_10240.FStar_TypeChecker_Env.qtbl_name_and_index);
                             FStar_TypeChecker_Env.normalized_eff_names =
                               (uu___1087_10240.FStar_TypeChecker_Env.normalized_eff_names);
                             FStar_TypeChecker_Env.fv_delta_depths =
                               (uu___1087_10240.FStar_TypeChecker_Env.fv_delta_depths);
                             FStar_TypeChecker_Env.proof_ns =
                               (uu___1087_10240.FStar_TypeChecker_Env.proof_ns);
                             FStar_TypeChecker_Env.synth_hook =
                               (uu___1087_10240.FStar_TypeChecker_Env.synth_hook);
                             FStar_TypeChecker_Env.splice =
                               (uu___1087_10240.FStar_TypeChecker_Env.splice);
                             FStar_TypeChecker_Env.mpreprocess =
                               (uu___1087_10240.FStar_TypeChecker_Env.mpreprocess);
                             FStar_TypeChecker_Env.postprocess =
                               (uu___1087_10240.FStar_TypeChecker_Env.postprocess);
                             FStar_TypeChecker_Env.is_native_tactic =
                               (uu___1087_10240.FStar_TypeChecker_Env.is_native_tactic);
                             FStar_TypeChecker_Env.identifier_info =
                               (uu___1087_10240.FStar_TypeChecker_Env.identifier_info);
                             FStar_TypeChecker_Env.tc_hooks =
                               (uu___1087_10240.FStar_TypeChecker_Env.tc_hooks);
                             FStar_TypeChecker_Env.dsenv =
                               (uu___1087_10240.FStar_TypeChecker_Env.dsenv);
                             FStar_TypeChecker_Env.nbe =
                               (uu___1087_10240.FStar_TypeChecker_Env.nbe);
                             FStar_TypeChecker_Env.strict_args_tab =
                               (uu___1087_10240.FStar_TypeChecker_Env.strict_args_tab);
                             FStar_TypeChecker_Env.erasable_types_tab =
                               (uu___1087_10240.FStar_TypeChecker_Env.erasable_types_tab)
                           }  in
                         let lift1 =
                           match lift with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some (uvs,lift1) ->
                               let uu____10273 =
                                 let uu____10278 =
                                   FStar_Syntax_Subst.univ_var_opening uvs
                                    in
                                 match uu____10278 with
                                 | (usubst,uvs1) ->
                                     let uu____10301 =
                                       FStar_TypeChecker_Env.push_univ_vars
                                         env1 uvs1
                                        in
                                     let uu____10302 =
                                       FStar_Syntax_Subst.subst usubst lift1
                                        in
                                     (uu____10301, uu____10302)
                                  in
                               (match uu____10273 with
                                | (env2,lift2) ->
                                    let uu____10307 =
                                      let uu____10314 =
                                        FStar_TypeChecker_Env.lookup_effect_lid
                                          env2
                                          sub1.FStar_Syntax_Syntax.source
                                         in
                                      monad_signature env2
                                        sub1.FStar_Syntax_Syntax.source
                                        uu____10314
                                       in
                                    (match uu____10307 with
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
                                             let uu____10340 =
                                               FStar_TypeChecker_Env.get_range
                                                 env2
                                                in
                                             let uu____10341 =
                                               let uu____10348 =
                                                 let uu____10349 =
                                                   let uu____10366 =
                                                     let uu____10377 =
                                                       FStar_Syntax_Syntax.as_arg
                                                         a_typ
                                                        in
                                                     let uu____10386 =
                                                       let uu____10397 =
                                                         FStar_Syntax_Syntax.as_arg
                                                           wp_a_typ
                                                          in
                                                       [uu____10397]  in
                                                     uu____10377 ::
                                                       uu____10386
                                                      in
                                                   (lift_wp1, uu____10366)
                                                    in
                                                 FStar_Syntax_Syntax.Tm_app
                                                   uu____10349
                                                  in
                                               FStar_Syntax_Syntax.mk
                                                 uu____10348
                                                in
                                             uu____10341
                                               FStar_Pervasives_Native.None
                                               uu____10340
                                              in
                                           repr_type
                                             sub1.FStar_Syntax_Syntax.target
                                             a_typ lift_wp_a
                                            in
                                         let expected_k1 =
                                           let uu____10445 =
                                             let uu____10454 =
                                               FStar_Syntax_Syntax.mk_binder
                                                 a1
                                                in
                                             let uu____10461 =
                                               let uu____10470 =
                                                 FStar_Syntax_Syntax.mk_binder
                                                   wp_a
                                                  in
                                               let uu____10477 =
                                                 let uu____10486 =
                                                   FStar_Syntax_Syntax.null_binder
                                                     repr_f
                                                    in
                                                 [uu____10486]  in
                                               uu____10470 :: uu____10477  in
                                             uu____10454 :: uu____10461  in
                                           let uu____10517 =
                                             FStar_Syntax_Syntax.mk_Total
                                               repr_result
                                              in
                                           FStar_Syntax_Util.arrow
                                             uu____10445 uu____10517
                                            in
                                         let uu____10520 =
                                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term
                                             env2 expected_k1
                                            in
                                         (match uu____10520 with
                                          | (expected_k2,uu____10530,uu____10531)
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
                                                   let uu____10539 =
                                                     FStar_Syntax_Subst.close_univ_vars
                                                       uvs lift3
                                                      in
                                                   (uvs, uu____10539))
                                                 in
                                              FStar_Pervasives_Native.Some
                                                lift3)))
                            in
                         ((let uu____10547 =
                             let uu____10549 =
                               let uu____10551 =
                                 FStar_All.pipe_right lift_wp
                                   FStar_Pervasives_Native.fst
                                  in
                               FStar_All.pipe_right uu____10551
                                 FStar_List.length
                                in
                             uu____10549 <> Prims.int_one  in
                           if uu____10547
                           then
                             let uu____10574 =
                               let uu____10580 =
                                 let uu____10582 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10584 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10586 =
                                   let uu____10588 =
                                     let uu____10590 =
                                       FStar_All.pipe_right lift_wp
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10590
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10588
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect wp must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10582 uu____10584 uu____10586
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10580)
                                in
                             FStar_Errors.raise_error uu____10574 r
                           else ());
                          (let uu____10617 =
                             (FStar_Util.is_some lift1) &&
                               (let uu____10620 =
                                  let uu____10622 =
                                    let uu____10625 =
                                      FStar_All.pipe_right lift1
                                        FStar_Util.must
                                       in
                                    FStar_All.pipe_right uu____10625
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____10622
                                    FStar_List.length
                                   in
                                uu____10620 <> Prims.int_one)
                              in
                           if uu____10617
                           then
                             let uu____10664 =
                               let uu____10670 =
                                 let uu____10672 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.source
                                    in
                                 let uu____10674 =
                                   FStar_Syntax_Print.lid_to_string
                                     sub1.FStar_Syntax_Syntax.target
                                    in
                                 let uu____10676 =
                                   let uu____10678 =
                                     let uu____10680 =
                                       let uu____10683 =
                                         FStar_All.pipe_right lift1
                                           FStar_Util.must
                                          in
                                       FStar_All.pipe_right uu____10683
                                         FStar_Pervasives_Native.fst
                                        in
                                     FStar_All.pipe_right uu____10680
                                       FStar_List.length
                                      in
                                   FStar_All.pipe_right uu____10678
                                     FStar_Util.string_of_int
                                    in
                                 FStar_Util.format3
                                   "Sub effect lift must be polymorphic in exactly 1 universe; %s ~> %s has %s universes"
                                   uu____10672 uu____10674 uu____10676
                                  in
                               (FStar_Errors.Fatal_TooManyUniverse,
                                 uu____10670)
                                in
                             FStar_Errors.raise_error uu____10664 r
                           else ());
                          (let uu___1124_10725 = sub1  in
                           {
                             FStar_Syntax_Syntax.source =
                               (uu___1124_10725.FStar_Syntax_Syntax.source);
                             FStar_Syntax_Syntax.target =
                               (uu___1124_10725.FStar_Syntax_Syntax.target);
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
    fun uu____10756  ->
      fun r  ->
        match uu____10756 with
        | (lid,uvs,tps,c) ->
            let env0 = env  in
            let uu____10779 =
              if (FStar_List.length uvs) = Prims.int_zero
              then (env, uvs, tps, c)
              else
                (let uu____10807 = FStar_Syntax_Subst.univ_var_opening uvs
                    in
                 match uu____10807 with
                 | (usubst,uvs1) ->
                     let tps1 = FStar_Syntax_Subst.subst_binders usubst tps
                        in
                     let c1 =
                       let uu____10838 =
                         FStar_Syntax_Subst.shift_subst
                           (FStar_List.length tps1) usubst
                          in
                       FStar_Syntax_Subst.subst_comp uu____10838 c  in
                     let uu____10847 =
                       FStar_TypeChecker_Env.push_univ_vars env uvs1  in
                     (uu____10847, uvs1, tps1, c1))
               in
            (match uu____10779 with
             | (env1,uvs1,tps1,c1) ->
                 let env2 = FStar_TypeChecker_Env.set_range env1 r  in
                 let uu____10867 = FStar_Syntax_Subst.open_comp tps1 c1  in
                 (match uu____10867 with
                  | (tps2,c2) ->
                      let uu____10882 =
                        FStar_TypeChecker_TcTerm.tc_tparams env2 tps2  in
                      (match uu____10882 with
                       | (tps3,env3,us) ->
                           let uu____10900 =
                             FStar_TypeChecker_TcTerm.tc_comp env3 c2  in
                           (match uu____10900 with
                            | (c3,u,g) ->
                                (FStar_TypeChecker_Rel.force_trivial_guard
                                   env3 g;
                                 (let expected_result_typ =
                                    match tps3 with
                                    | (x,uu____10926)::uu____10927 ->
                                        FStar_Syntax_Syntax.bv_to_name x
                                    | uu____10946 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                            "Effect abbreviations must bind at least the result type")
                                          r
                                     in
                                  let def_result_typ =
                                    FStar_Syntax_Util.comp_result c3  in
                                  let uu____10954 =
                                    let uu____10956 =
                                      FStar_TypeChecker_Rel.teq_nosmt_force
                                        env3 expected_result_typ
                                        def_result_typ
                                       in
                                    Prims.op_Negation uu____10956  in
                                  if uu____10954
                                  then
                                    let uu____10959 =
                                      let uu____10965 =
                                        let uu____10967 =
                                          FStar_Syntax_Print.term_to_string
                                            expected_result_typ
                                           in
                                        let uu____10969 =
                                          FStar_Syntax_Print.term_to_string
                                            def_result_typ
                                           in
                                        FStar_Util.format2
                                          "Result type of effect abbreviation `%s` does not match the result type of its definition `%s`"
                                          uu____10967 uu____10969
                                         in
                                      (FStar_Errors.Fatal_EffectAbbreviationResultTypeMismatch,
                                        uu____10965)
                                       in
                                    FStar_Errors.raise_error uu____10959 r
                                  else ());
                                 (let tps4 =
                                    FStar_Syntax_Subst.close_binders tps3  in
                                  let c4 =
                                    FStar_Syntax_Subst.close_comp tps4 c3  in
                                  let uu____10977 =
                                    let uu____10978 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_arrow
                                           (tps4, c4))
                                        FStar_Pervasives_Native.None r
                                       in
                                    FStar_TypeChecker_Util.generalize_universes
                                      env0 uu____10978
                                     in
                                  match uu____10977 with
                                  | (uvs2,t) ->
                                      let uu____11007 =
                                        let uu____11012 =
                                          let uu____11025 =
                                            let uu____11026 =
                                              FStar_Syntax_Subst.compress t
                                               in
                                            uu____11026.FStar_Syntax_Syntax.n
                                             in
                                          (tps4, uu____11025)  in
                                        match uu____11012 with
                                        | ([],FStar_Syntax_Syntax.Tm_arrow
                                           (uu____11041,c5)) -> ([], c5)
                                        | (uu____11083,FStar_Syntax_Syntax.Tm_arrow
                                           (tps5,c5)) -> (tps5, c5)
                                        | uu____11122 ->
                                            failwith
                                              "Impossible (t is an arrow)"
                                         in
                                      (match uu____11007 with
                                       | (tps5,c5) ->
                                           (if
                                              (FStar_List.length uvs2) <>
                                                Prims.int_one
                                            then
                                              (let uu____11154 =
                                                 FStar_Syntax_Subst.open_univ_vars
                                                   uvs2 t
                                                  in
                                               match uu____11154 with
                                               | (uu____11159,t1) ->
                                                   let uu____11161 =
                                                     let uu____11167 =
                                                       let uu____11169 =
                                                         FStar_Syntax_Print.lid_to_string
                                                           lid
                                                          in
                                                       let uu____11171 =
                                                         FStar_All.pipe_right
                                                           (FStar_List.length
                                                              uvs2)
                                                           FStar_Util.string_of_int
                                                          in
                                                       let uu____11175 =
                                                         FStar_Syntax_Print.term_to_string
                                                           t1
                                                          in
                                                       FStar_Util.format3
                                                         "Effect abbreviations must be polymorphic in exactly 1 universe; %s has %s universes (%s)"
                                                         uu____11169
                                                         uu____11171
                                                         uu____11175
                                                        in
                                                     (FStar_Errors.Fatal_TooManyUniverse,
                                                       uu____11167)
                                                      in
                                                   FStar_Errors.raise_error
                                                     uu____11161 r)
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
              let uu____11217 = FStar_Ident.string_of_lid m  in
              let uu____11219 = FStar_Ident.string_of_lid n1  in
              let uu____11221 = FStar_Ident.string_of_lid p  in
              FStar_Util.format3 "(%s, %s) |> %s)" uu____11217 uu____11219
                uu____11221
               in
            let r = (FStar_Pervasives_Native.snd ts).FStar_Syntax_Syntax.pos
               in
            (let uu____11230 =
               FStar_TypeChecker_Env.is_user_reifiable_effect env p  in
             if uu____11230
             then
               let uu____11233 =
                 let uu____11239 =
                   let uu____11241 = FStar_Ident.string_of_lid p  in
                   FStar_Util.format2
                     "Error typechecking the polymonadic bind %s, the final effect %s is reifiable and reification of polymondic binds is not yet implemented"
                     eff_name uu____11241
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____11239)  in
               FStar_Errors.raise_error uu____11233 r
             else ());
            (let uu____11247 =
               check_and_gen env eff_name "polymonadic_bind"
                 (Prims.of_int (2)) ts
                in
             match uu____11247 with
             | (us,t,ty) ->
                 let uu____11263 = FStar_Syntax_Subst.open_univ_vars us ty
                    in
                 (match uu____11263 with
                  | (us1,ty1) ->
                      let env1 = FStar_TypeChecker_Env.push_univ_vars env us1
                         in
                      let uu____11275 =
                        let uu____11280 = FStar_Syntax_Util.type_u ()  in
                        FStar_All.pipe_right uu____11280
                          (fun uu____11297  ->
                             match uu____11297 with
                             | (t1,u) ->
                                 let uu____11308 =
                                   let uu____11309 =
                                     FStar_Syntax_Syntax.gen_bv "a"
                                       FStar_Pervasives_Native.None t1
                                      in
                                   FStar_All.pipe_right uu____11309
                                     FStar_Syntax_Syntax.mk_binder
                                    in
                                 (uu____11308, u))
                         in
                      (match uu____11275 with
                       | (a,u_a) ->
                           let uu____11317 =
                             let uu____11322 = FStar_Syntax_Util.type_u ()
                                in
                             FStar_All.pipe_right uu____11322
                               (fun uu____11339  ->
                                  match uu____11339 with
                                  | (t1,u) ->
                                      let uu____11350 =
                                        let uu____11351 =
                                          FStar_Syntax_Syntax.gen_bv "b"
                                            FStar_Pervasives_Native.None t1
                                           in
                                        FStar_All.pipe_right uu____11351
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11350, u))
                              in
                           (match uu____11317 with
                            | (b,u_b) ->
                                let rest_bs =
                                  let uu____11368 =
                                    let uu____11369 =
                                      FStar_Syntax_Subst.compress ty1  in
                                    uu____11369.FStar_Syntax_Syntax.n  in
                                  match uu____11368 with
                                  | FStar_Syntax_Syntax.Tm_arrow
                                      (bs,uu____11381) when
                                      (FStar_List.length bs) >=
                                        (Prims.of_int (4))
                                      ->
                                      let uu____11409 =
                                        FStar_Syntax_Subst.open_binders bs
                                         in
                                      (match uu____11409 with
                                       | (a',uu____11419)::(b',uu____11421)::bs1
                                           ->
                                           let uu____11451 =
                                             let uu____11452 =
                                               FStar_All.pipe_right bs1
                                                 (FStar_List.splitAt
                                                    ((FStar_List.length bs1)
                                                       - (Prims.of_int (2))))
                                                in
                                             FStar_All.pipe_right uu____11452
                                               FStar_Pervasives_Native.fst
                                              in
                                           let uu____11518 =
                                             let uu____11531 =
                                               let uu____11534 =
                                                 let uu____11535 =
                                                   let uu____11542 =
                                                     let uu____11545 =
                                                       FStar_All.pipe_right a
                                                         FStar_Pervasives_Native.fst
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____11545
                                                       FStar_Syntax_Syntax.bv_to_name
                                                      in
                                                   (a', uu____11542)  in
                                                 FStar_Syntax_Syntax.NT
                                                   uu____11535
                                                  in
                                               let uu____11558 =
                                                 let uu____11561 =
                                                   let uu____11562 =
                                                     let uu____11569 =
                                                       let uu____11572 =
                                                         FStar_All.pipe_right
                                                           b
                                                           FStar_Pervasives_Native.fst
                                                          in
                                                       FStar_All.pipe_right
                                                         uu____11572
                                                         FStar_Syntax_Syntax.bv_to_name
                                                        in
                                                     (b', uu____11569)  in
                                                   FStar_Syntax_Syntax.NT
                                                     uu____11562
                                                    in
                                                 [uu____11561]  in
                                               uu____11534 :: uu____11558  in
                                             FStar_Syntax_Subst.subst_binders
                                               uu____11531
                                              in
                                           FStar_All.pipe_right uu____11451
                                             uu____11518)
                                  | uu____11593 ->
                                      let uu____11594 =
                                        let uu____11600 =
                                          let uu____11602 =
                                            FStar_Syntax_Print.tag_of_term
                                              ty1
                                             in
                                          let uu____11604 =
                                            FStar_Syntax_Print.term_to_string
                                              ty1
                                             in
                                          FStar_Util.format3
                                            "Type of %s is not an arrow with >= 4 binders (%s::%s)"
                                            eff_name uu____11602 uu____11604
                                           in
                                        (FStar_Errors.Fatal_UnexpectedEffect,
                                          uu____11600)
                                         in
                                      FStar_Errors.raise_error uu____11594 r
                                   in
                                let bs = a :: b :: rest_bs  in
                                let uu____11637 =
                                  let uu____11648 =
                                    let uu____11653 =
                                      FStar_TypeChecker_Env.push_binders env1
                                        bs
                                       in
                                    let uu____11654 =
                                      let uu____11655 =
                                        FStar_All.pipe_right a
                                          FStar_Pervasives_Native.fst
                                         in
                                      FStar_All.pipe_right uu____11655
                                        FStar_Syntax_Syntax.bv_to_name
                                       in
                                    FStar_TypeChecker_Util.fresh_effect_repr_en
                                      uu____11653 r m u_a uu____11654
                                     in
                                  match uu____11648 with
                                  | (repr,g) ->
                                      let uu____11676 =
                                        let uu____11683 =
                                          FStar_Syntax_Syntax.gen_bv "f"
                                            FStar_Pervasives_Native.None repr
                                           in
                                        FStar_All.pipe_right uu____11683
                                          FStar_Syntax_Syntax.mk_binder
                                         in
                                      (uu____11676, g)
                                   in
                                (match uu____11637 with
                                 | (f,guard_f) ->
                                     let uu____11715 =
                                       let x_a =
                                         let uu____11733 =
                                           let uu____11734 =
                                             let uu____11735 =
                                               FStar_All.pipe_right a
                                                 FStar_Pervasives_Native.fst
                                                in
                                             FStar_All.pipe_right uu____11735
                                               FStar_Syntax_Syntax.bv_to_name
                                              in
                                           FStar_Syntax_Syntax.gen_bv "x"
                                             FStar_Pervasives_Native.None
                                             uu____11734
                                            in
                                         FStar_All.pipe_right uu____11733
                                           FStar_Syntax_Syntax.mk_binder
                                          in
                                       let uu____11751 =
                                         let uu____11756 =
                                           FStar_TypeChecker_Env.push_binders
                                             env1
                                             (FStar_List.append bs [x_a])
                                            in
                                         let uu____11775 =
                                           let uu____11776 =
                                             FStar_All.pipe_right b
                                               FStar_Pervasives_Native.fst
                                              in
                                           FStar_All.pipe_right uu____11776
                                             FStar_Syntax_Syntax.bv_to_name
                                            in
                                         FStar_TypeChecker_Util.fresh_effect_repr_en
                                           uu____11756 r n1 u_b uu____11775
                                          in
                                       match uu____11751 with
                                       | (repr,g) ->
                                           let uu____11797 =
                                             let uu____11804 =
                                               let uu____11805 =
                                                 let uu____11806 =
                                                   let uu____11809 =
                                                     let uu____11812 =
                                                       FStar_TypeChecker_Env.new_u_univ
                                                         ()
                                                        in
                                                     FStar_Pervasives_Native.Some
                                                       uu____11812
                                                      in
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr uu____11809
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   [x_a] uu____11806
                                                  in
                                               FStar_Syntax_Syntax.gen_bv "g"
                                                 FStar_Pervasives_Native.None
                                                 uu____11805
                                                in
                                             FStar_All.pipe_right uu____11804
                                               FStar_Syntax_Syntax.mk_binder
                                              in
                                           (uu____11797, g)
                                        in
                                     (match uu____11715 with
                                      | (g,guard_g) ->
                                          let uu____11856 =
                                            let uu____11861 =
                                              FStar_TypeChecker_Env.push_binders
                                                env1 bs
                                               in
                                            let uu____11862 =
                                              let uu____11863 =
                                                FStar_All.pipe_right b
                                                  FStar_Pervasives_Native.fst
                                                 in
                                              FStar_All.pipe_right
                                                uu____11863
                                                FStar_Syntax_Syntax.bv_to_name
                                               in
                                            FStar_TypeChecker_Util.fresh_effect_repr_en
                                              uu____11861 r p u_b uu____11862
                                             in
                                          (match uu____11856 with
                                           | (repr,guard_repr) ->
                                               let k =
                                                 let uu____11881 =
                                                   FStar_Syntax_Syntax.mk_Total'
                                                     repr
                                                     (FStar_Pervasives_Native.Some
                                                        u_b)
                                                    in
                                                 FStar_Syntax_Util.arrow
                                                   (FStar_List.append bs
                                                      [f; g]) uu____11881
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
                                                (let uu____11911 =
                                                   FStar_All.pipe_left
                                                     (FStar_TypeChecker_Env.debug
                                                        env1)
                                                     FStar_Options.Extreme
                                                    in
                                                 if uu____11911
                                                 then
                                                   let uu____11915 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       (us1, t)
                                                      in
                                                   let uu____11921 =
                                                     FStar_Syntax_Print.tscheme_to_string
                                                       (us1, k)
                                                      in
                                                   FStar_Util.print3
                                                     "Polymonadic bind %s after typechecking (%s::%s)\n"
                                                     eff_name uu____11915
                                                     uu____11921
                                                 else ());
                                                (let uu____11931 =
                                                   let uu____11937 =
                                                     FStar_Util.format1
                                                       "Polymonadic binds (%s in this case) is a bleeding edge F* feature;it is subject to some redesign in the future. Please keep us informed (on github etc.) about how you are using it"
                                                       eff_name
                                                      in
                                                   (FStar_Errors.Warning_BleedingEdge_Feature,
                                                     uu____11937)
                                                    in
                                                 FStar_Errors.log_issue r
                                                   uu____11931);
                                                (let k1 =
                                                   FStar_All.pipe_right k
                                                     (FStar_TypeChecker_Normalize.remove_uvar_solutions
                                                        env1)
                                                    in
                                                 check_no_subtyping_for_layered_combinator
                                                   env1 k1
                                                   FStar_Pervasives_Native.None;
                                                 (let uu____11943 =
                                                    let uu____11944 =
                                                      FStar_Syntax_Subst.close_univ_vars
                                                        us1 k1
                                                       in
                                                    (us1, uu____11944)  in
                                                  ((us1, t), uu____11943)))))))))))
  