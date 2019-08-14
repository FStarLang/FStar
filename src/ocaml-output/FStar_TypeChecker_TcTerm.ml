open Prims
let (instantiate_both :
  FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___8_5 = env  in
    {
      FStar_TypeChecker_Env.solver = (uu___8_5.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___8_5.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___8_5.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___8_5.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___8_5.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___8_5.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___8_5.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___8_5.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab = (uu___8_5.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___8_5.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___8_5.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = true;
      FStar_TypeChecker_Env.effects =
        (uu___8_5.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___8_5.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___8_5.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___8_5.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___8_5.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq = (uu___8_5.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___8_5.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___8_5.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___8_5.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___8_5.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 = (uu___8_5.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___8_5.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___8_5.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___8_5.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___8_5.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___8_5.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___8_5.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___8_5.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___8_5.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___8_5.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___8_5.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___8_5.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___8_5.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___8_5.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice = (uu___8_5.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___8_5.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___8_5.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___8_5.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___8_5.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___8_5.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___8_5.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___8_5.FStar_TypeChecker_Env.strict_args_tab)
    }
  
let (no_inst : FStar_TypeChecker_Env.env -> FStar_TypeChecker_Env.env) =
  fun env  ->
    let uu___11_13 = env  in
    {
      FStar_TypeChecker_Env.solver =
        (uu___11_13.FStar_TypeChecker_Env.solver);
      FStar_TypeChecker_Env.range = (uu___11_13.FStar_TypeChecker_Env.range);
      FStar_TypeChecker_Env.curmodule =
        (uu___11_13.FStar_TypeChecker_Env.curmodule);
      FStar_TypeChecker_Env.gamma = (uu___11_13.FStar_TypeChecker_Env.gamma);
      FStar_TypeChecker_Env.gamma_sig =
        (uu___11_13.FStar_TypeChecker_Env.gamma_sig);
      FStar_TypeChecker_Env.gamma_cache =
        (uu___11_13.FStar_TypeChecker_Env.gamma_cache);
      FStar_TypeChecker_Env.modules =
        (uu___11_13.FStar_TypeChecker_Env.modules);
      FStar_TypeChecker_Env.expected_typ =
        (uu___11_13.FStar_TypeChecker_Env.expected_typ);
      FStar_TypeChecker_Env.sigtab =
        (uu___11_13.FStar_TypeChecker_Env.sigtab);
      FStar_TypeChecker_Env.attrtab =
        (uu___11_13.FStar_TypeChecker_Env.attrtab);
      FStar_TypeChecker_Env.is_pattern =
        (uu___11_13.FStar_TypeChecker_Env.is_pattern);
      FStar_TypeChecker_Env.instantiate_imp = false;
      FStar_TypeChecker_Env.effects =
        (uu___11_13.FStar_TypeChecker_Env.effects);
      FStar_TypeChecker_Env.generalize =
        (uu___11_13.FStar_TypeChecker_Env.generalize);
      FStar_TypeChecker_Env.letrecs =
        (uu___11_13.FStar_TypeChecker_Env.letrecs);
      FStar_TypeChecker_Env.top_level =
        (uu___11_13.FStar_TypeChecker_Env.top_level);
      FStar_TypeChecker_Env.check_uvars =
        (uu___11_13.FStar_TypeChecker_Env.check_uvars);
      FStar_TypeChecker_Env.use_eq =
        (uu___11_13.FStar_TypeChecker_Env.use_eq);
      FStar_TypeChecker_Env.is_iface =
        (uu___11_13.FStar_TypeChecker_Env.is_iface);
      FStar_TypeChecker_Env.admit = (uu___11_13.FStar_TypeChecker_Env.admit);
      FStar_TypeChecker_Env.lax = (uu___11_13.FStar_TypeChecker_Env.lax);
      FStar_TypeChecker_Env.lax_universes =
        (uu___11_13.FStar_TypeChecker_Env.lax_universes);
      FStar_TypeChecker_Env.phase1 =
        (uu___11_13.FStar_TypeChecker_Env.phase1);
      FStar_TypeChecker_Env.failhard =
        (uu___11_13.FStar_TypeChecker_Env.failhard);
      FStar_TypeChecker_Env.nosynth =
        (uu___11_13.FStar_TypeChecker_Env.nosynth);
      FStar_TypeChecker_Env.uvar_subtyping =
        (uu___11_13.FStar_TypeChecker_Env.uvar_subtyping);
      FStar_TypeChecker_Env.tc_term =
        (uu___11_13.FStar_TypeChecker_Env.tc_term);
      FStar_TypeChecker_Env.type_of =
        (uu___11_13.FStar_TypeChecker_Env.type_of);
      FStar_TypeChecker_Env.universe_of =
        (uu___11_13.FStar_TypeChecker_Env.universe_of);
      FStar_TypeChecker_Env.check_type_of =
        (uu___11_13.FStar_TypeChecker_Env.check_type_of);
      FStar_TypeChecker_Env.use_bv_sorts =
        (uu___11_13.FStar_TypeChecker_Env.use_bv_sorts);
      FStar_TypeChecker_Env.qtbl_name_and_index =
        (uu___11_13.FStar_TypeChecker_Env.qtbl_name_and_index);
      FStar_TypeChecker_Env.normalized_eff_names =
        (uu___11_13.FStar_TypeChecker_Env.normalized_eff_names);
      FStar_TypeChecker_Env.fv_delta_depths =
        (uu___11_13.FStar_TypeChecker_Env.fv_delta_depths);
      FStar_TypeChecker_Env.proof_ns =
        (uu___11_13.FStar_TypeChecker_Env.proof_ns);
      FStar_TypeChecker_Env.synth_hook =
        (uu___11_13.FStar_TypeChecker_Env.synth_hook);
      FStar_TypeChecker_Env.splice =
        (uu___11_13.FStar_TypeChecker_Env.splice);
      FStar_TypeChecker_Env.postprocess =
        (uu___11_13.FStar_TypeChecker_Env.postprocess);
      FStar_TypeChecker_Env.is_native_tactic =
        (uu___11_13.FStar_TypeChecker_Env.is_native_tactic);
      FStar_TypeChecker_Env.identifier_info =
        (uu___11_13.FStar_TypeChecker_Env.identifier_info);
      FStar_TypeChecker_Env.tc_hooks =
        (uu___11_13.FStar_TypeChecker_Env.tc_hooks);
      FStar_TypeChecker_Env.dsenv = (uu___11_13.FStar_TypeChecker_Env.dsenv);
      FStar_TypeChecker_Env.nbe = (uu___11_13.FStar_TypeChecker_Env.nbe);
      FStar_TypeChecker_Env.strict_args_tab =
        (uu___11_13.FStar_TypeChecker_Env.strict_args_tab)
    }
  
let (mk_lex_list :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun vs  ->
    FStar_List.fold_right
      (fun v1  ->
         fun tl1  ->
           let r =
             if tl1.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
             then v1.FStar_Syntax_Syntax.pos
             else
               FStar_Range.union_ranges v1.FStar_Syntax_Syntax.pos
                 tl1.FStar_Syntax_Syntax.pos
              in
           let uu____49 =
             let uu____54 =
               let uu____55 = FStar_Syntax_Syntax.as_arg v1  in
               let uu____64 =
                 let uu____75 = FStar_Syntax_Syntax.as_arg tl1  in [uu____75]
                  in
               uu____55 :: uu____64  in
             FStar_Syntax_Syntax.mk_Tm_app FStar_Syntax_Util.lex_pair
               uu____54
              in
           uu____49 FStar_Pervasives_Native.None r) vs
      FStar_Syntax_Util.lex_top
  
let (is_eq :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    Prims.bool)
  =
  fun uu___0_116  ->
    match uu___0_116 with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality ) -> true
    | uu____121 -> false
  
let steps :
  'Auu____130 . 'Auu____130 -> FStar_TypeChecker_Env.step Prims.list =
  fun env  ->
    [FStar_TypeChecker_Env.Beta;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.NoFullNorm]
  
let (norm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t  -> FStar_TypeChecker_Normalize.normalize (steps env) env t
  
let (norm_c :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  =
  fun env  ->
    fun c  -> FStar_TypeChecker_Normalize.normalize_comp (steps env) env c
  
let (check_no_escape :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.bv Prims.list ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun head_opt  ->
    fun env  ->
      fun fvs  ->
        fun kt  ->
          let rec aux try_norm t =
            match fvs with
            | [] -> (t, FStar_TypeChecker_Env.trivial_guard)
            | uu____218 ->
                let t1 = if try_norm then norm env t else t  in
                let fvs' = FStar_Syntax_Free.names t1  in
                let uu____232 =
                  FStar_List.tryFind (fun x  -> FStar_Util.set_mem x fvs')
                    fvs
                   in
                (match uu____232 with
                 | FStar_Pervasives_Native.None  ->
                     (t1, FStar_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some x ->
                     if Prims.op_Negation try_norm
                     then aux true t1
                     else
                       (let fail1 uu____259 =
                          let msg =
                            match head_opt with
                            | FStar_Pervasives_Native.None  ->
                                let uu____263 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                FStar_Util.format1
                                  "Bound variables '%s' escapes; add a type annotation"
                                  uu____263
                            | FStar_Pervasives_Native.Some head1 ->
                                let uu____267 =
                                  FStar_Syntax_Print.bv_to_string x  in
                                let uu____269 =
                                  FStar_TypeChecker_Normalize.term_to_string
                                    env head1
                                   in
                                FStar_Util.format2
                                  "Bound variables '%s' in the type of '%s' escape because of impure applications; add explicit let-bindings"
                                  uu____267 uu____269
                             in
                          let uu____272 = FStar_TypeChecker_Env.get_range env
                             in
                          FStar_Errors.raise_error
                            (FStar_Errors.Fatal_EscapedBoundVar, msg)
                            uu____272
                           in
                        let uu____278 =
                          let uu____291 = FStar_TypeChecker_Env.get_range env
                             in
                          let uu____292 =
                            let uu____293 = FStar_Syntax_Util.type_u ()  in
                            FStar_All.pipe_left FStar_Pervasives_Native.fst
                              uu____293
                             in
                          FStar_TypeChecker_Util.new_implicit_var "no escape"
                            uu____291 env uu____292
                           in
                        match uu____278 with
                        | (s,uu____308,g0) ->
                            let uu____322 =
                              FStar_TypeChecker_Rel.try_teq true env t1 s  in
                            (match uu____322 with
                             | FStar_Pervasives_Native.Some g ->
                                 let g1 =
                                   let uu____332 =
                                     FStar_TypeChecker_Env.conj_guard g g0
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____332
                                    in
                                 (s, g1)
                             | uu____333 -> fail1 ())))
             in
          aux false kt
  
let push_binding :
  'Auu____344 .
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.bv * 'Auu____344) -> FStar_TypeChecker_Env.env
  =
  fun env  ->
    fun b  ->
      FStar_TypeChecker_Env.push_bv env (FStar_Pervasives_Native.fst b)
  
let (maybe_extend_subst :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.subst_t)
  =
  fun s  ->
    fun b  ->
      fun v1  ->
        let uu____399 = FStar_Syntax_Syntax.is_null_binder b  in
        if uu____399
        then s
        else (FStar_Syntax_Syntax.NT ((FStar_Pervasives_Native.fst b), v1))
          :: s
  
let (set_lcomp_result :
  FStar_TypeChecker_Common.lcomp ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_TypeChecker_Common.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_TypeChecker_Common.apply_lcomp
        (fun c  -> FStar_Syntax_Util.set_result_typ c t) (fun g  -> g)
        (let uu___66_429 = lc  in
         {
           FStar_TypeChecker_Common.eff_name =
             (uu___66_429.FStar_TypeChecker_Common.eff_name);
           FStar_TypeChecker_Common.res_typ = t;
           FStar_TypeChecker_Common.cflags =
             (uu___66_429.FStar_TypeChecker_Common.cflags);
           FStar_TypeChecker_Common.comp_thunk =
             (uu___66_429.FStar_TypeChecker_Common.comp_thunk)
         })
  
let (memo_tk :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.term)
  = fun e  -> fun t  -> e 
let (value_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.typ,FStar_TypeChecker_Common.lcomp)
        FStar_Util.either ->
        FStar_TypeChecker_Common.guard_t ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun tlc  ->
        fun guard  ->
          FStar_TypeChecker_Env.def_check_guard_wf e.FStar_Syntax_Syntax.pos
            "value_check_expected_typ" env guard;
          (let lc =
             match tlc with
             | FStar_Util.Inl t ->
                 let uu____486 = FStar_Syntax_Syntax.mk_Total t  in
                 FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                   uu____486
             | FStar_Util.Inr lc -> lc  in
           let t = lc.FStar_TypeChecker_Common.res_typ  in
           let uu____489 =
             let uu____496 = FStar_TypeChecker_Env.expected_typ env  in
             match uu____496 with
             | FStar_Pervasives_Native.None  -> ((memo_tk e t), lc, guard)
             | FStar_Pervasives_Native.Some t' ->
                 let uu____506 =
                   FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc
                     t'
                    in
                 (match uu____506 with
                  | (e1,lc1) ->
                      let t1 = lc1.FStar_TypeChecker_Common.res_typ  in
                      let uu____520 =
                        FStar_TypeChecker_Util.check_and_ascribe env e1 t1 t'
                         in
                      (match uu____520 with
                       | (e2,g) ->
                           ((let uu____534 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.High
                                in
                             if uu____534
                             then
                               let uu____537 =
                                 FStar_Syntax_Print.term_to_string t1  in
                               let uu____539 =
                                 FStar_Syntax_Print.term_to_string t'  in
                               let uu____541 =
                                 FStar_TypeChecker_Rel.guard_to_string env g
                                  in
                               let uu____543 =
                                 FStar_TypeChecker_Rel.guard_to_string env
                                   guard
                                  in
                               FStar_Util.print4
                                 "check_and_ascribe: type is %s<:%s \tguard is %s, %s\n"
                                 uu____537 uu____539 uu____541 uu____543
                             else ());
                            (let msg =
                               let uu____555 =
                                 FStar_TypeChecker_Env.is_trivial_guard_formula
                                   g
                                  in
                               if uu____555
                               then FStar_Pervasives_Native.None
                               else
                                 FStar_All.pipe_left
                                   (fun _584  ->
                                      FStar_Pervasives_Native.Some _584)
                                   (FStar_TypeChecker_Err.subtyping_failed
                                      env t1 t')
                                in
                             let g1 =
                               FStar_TypeChecker_Env.conj_guard g guard  in
                             let uu____586 =
                               let uu____591 =
                                 (FStar_All.pipe_right tlc FStar_Util.is_left)
                                   &&
                                   (FStar_TypeChecker_Util.should_return env
                                      (FStar_Pervasives_Native.Some e2) lc1)
                                  in
                               if uu____591
                               then
                                 let uu____603 =
                                   FStar_TypeChecker_Util.lcomp_univ_opt lc1
                                    in
                                 match uu____603 with
                                 | (u_opt,g_lc) ->
                                     let uu____620 =
                                       let uu____621 =
                                         FStar_TypeChecker_Util.return_value
                                           env u_opt t1 e2
                                          in
                                       FStar_All.pipe_right uu____621
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let uu____622 =
                                       FStar_TypeChecker_Env.conj_guard g1
                                         g_lc
                                        in
                                     (uu____620, uu____622)
                               else (lc1, g1)  in
                             match uu____586 with
                             | (lc2,g2) ->
                                 let uu____633 =
                                   FStar_TypeChecker_Util.strengthen_precondition
                                     msg env e2 lc2 g2
                                    in
                                 (match uu____633 with
                                  | (lc3,g3) ->
                                      let uu____646 = set_lcomp_result lc3 t'
                                         in
                                      ((memo_tk e2 t'), uu____646, g3))))))
              in
           match uu____489 with | (e1,lc1,g) -> (e1, lc1, g))
  
let (comp_check_expected_typ :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun lc  ->
        let uu____684 = FStar_TypeChecker_Env.expected_typ env  in
        match uu____684 with
        | FStar_Pervasives_Native.None  ->
            (e, lc, FStar_TypeChecker_Env.trivial_guard)
        | FStar_Pervasives_Native.Some t ->
            let uu____694 =
              FStar_TypeChecker_Util.maybe_coerce_bool_to_type env e lc t  in
            (match uu____694 with
             | (e1,lc1) ->
                 FStar_TypeChecker_Util.weaken_result_typ env e1 lc1 t)
  
let (check_expected_effect :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp) ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun copt  ->
      fun ec  ->
        let uu____747 = ec  in
        match uu____747 with
        | (e,c) ->
            let tot_or_gtot c1 =
              let uu____770 = FStar_Syntax_Util.is_pure_comp c1  in
              if uu____770
              then
                FStar_Syntax_Syntax.mk_Total
                  (FStar_Syntax_Util.comp_result c1)
              else
                (let uu____775 = FStar_Syntax_Util.is_pure_or_ghost_comp c1
                    in
                 if uu____775
                 then
                   FStar_Syntax_Syntax.mk_GTotal
                     (FStar_Syntax_Util.comp_result c1)
                 else failwith "Impossible: Expected pure_or_ghost comp")
               in
            let uu____781 =
              let ct = FStar_Syntax_Util.comp_result c  in
              match copt with
              | FStar_Pervasives_Native.Some uu____805 ->
                  (copt, c, FStar_Pervasives_Native.None)
              | FStar_Pervasives_Native.None  ->
                  let uu____810 =
                    ((FStar_Options.ml_ish ()) &&
                       (FStar_Ident.lid_equals
                          FStar_Parser_Const.effect_ALL_lid
                          (FStar_Syntax_Util.comp_effect_name c)))
                      ||
                      (((FStar_Options.ml_ish ()) &&
                          env.FStar_TypeChecker_Env.lax)
                         &&
                         (let uu____813 =
                            FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                          Prims.op_Negation uu____813))
                     in
                  if uu____810
                  then
                    let uu____826 =
                      let uu____829 =
                        FStar_Syntax_Util.ml_comp ct
                          e.FStar_Syntax_Syntax.pos
                         in
                      FStar_Pervasives_Native.Some uu____829  in
                    (uu____826, c, FStar_Pervasives_Native.None)
                  else
                    (let uu____836 = FStar_Syntax_Util.is_tot_or_gtot_comp c
                        in
                     if uu____836
                     then
                       let uu____849 = tot_or_gtot c  in
                       (FStar_Pervasives_Native.None, uu____849,
                         FStar_Pervasives_Native.None)
                     else
                       (let uu____856 =
                          FStar_Syntax_Util.is_pure_or_ghost_comp c  in
                        if uu____856
                        then
                          let uu____869 =
                            let uu____872 = tot_or_gtot c  in
                            FStar_Pervasives_Native.Some uu____872  in
                          (uu____869, c, FStar_Pervasives_Native.None)
                        else
                          (let uu____879 =
                             FStar_Options.trivial_pre_for_unannotated_effectful_fns
                               ()
                              in
                           if uu____879
                           then
                             let uu____892 =
                               let uu____895 =
                                 FStar_TypeChecker_Util.check_trivial_precondition
                                   env c
                                  in
                               match uu____895 with
                               | (uu____904,uu____905,g) ->
                                   FStar_Pervasives_Native.Some g
                                in
                             (FStar_Pervasives_Native.None, c, uu____892)
                           else
                             (FStar_Pervasives_Native.None, c,
                               FStar_Pervasives_Native.None))))
               in
            (match uu____781 with
             | (expected_c_opt,c1,gopt) ->
                 let c2 = norm_c env c1  in
                 (match expected_c_opt with
                  | FStar_Pervasives_Native.None  ->
                      (e, c2,
                        ((match gopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_TypeChecker_Env.trivial_guard
                          | FStar_Pervasives_Native.Some g -> g)))
                  | FStar_Pervasives_Native.Some expected_c ->
                      ((match gopt with
                        | FStar_Pervasives_Native.None  -> ()
                        | FStar_Pervasives_Native.Some uu____944 ->
                            failwith
                              "Impossible! check_expected_effect, gopt should have been None");
                       (let c3 =
                          let uu____947 =
                            FStar_TypeChecker_Common.lcomp_of_comp c2  in
                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                            env e uu____947
                           in
                        let uu____948 =
                          FStar_TypeChecker_Common.lcomp_comp c3  in
                        match uu____948 with
                        | (c4,g_c) ->
                            ((let uu____962 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env)
                                  FStar_Options.Low
                                 in
                              if uu____962
                              then
                                let uu____966 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____968 =
                                  FStar_Syntax_Print.comp_to_string c4  in
                                let uu____970 =
                                  FStar_Syntax_Print.comp_to_string
                                    expected_c
                                   in
                                FStar_Util.print3
                                  "In check_expected_effect, asking rel to solve the problem on e=(%s) and c=(%s) and expected_c=(%s)\n"
                                  uu____966 uu____968 uu____970
                              else ());
                             (let uu____975 =
                                FStar_TypeChecker_Util.check_comp env e c4
                                  expected_c
                                 in
                              match uu____975 with
                              | (e1,uu____989,g) ->
                                  let g1 =
                                    let uu____992 =
                                      FStar_TypeChecker_Env.get_range env  in
                                    FStar_TypeChecker_Util.label_guard
                                      uu____992
                                      "could not prove post-condition" g
                                     in
                                  ((let uu____995 =
                                      FStar_TypeChecker_Env.debug env
                                        FStar_Options.Low
                                       in
                                    if uu____995
                                    then
                                      let uu____998 =
                                        FStar_Range.string_of_range
                                          e1.FStar_Syntax_Syntax.pos
                                         in
                                      let uu____1000 =
                                        FStar_TypeChecker_Rel.guard_to_string
                                          env g1
                                         in
                                      FStar_Util.print2
                                        "(%s) DONE check_expected_effect;\n\tguard is: %s\n"
                                        uu____998 uu____1000
                                    else ());
                                   (let e2 =
                                      FStar_TypeChecker_Util.maybe_lift env
                                        e1
                                        (FStar_Syntax_Util.comp_effect_name
                                           c4)
                                        (FStar_Syntax_Util.comp_effect_name
                                           expected_c)
                                        (FStar_Syntax_Util.comp_result c4)
                                       in
                                    let uu____1006 =
                                      FStar_TypeChecker_Env.conj_guard g_c g1
                                       in
                                    (e2, expected_c, uu____1006)))))))))
  
let no_logical_guard :
  'Auu____1016 'Auu____1017 .
    FStar_TypeChecker_Env.env ->
      ('Auu____1016 * 'Auu____1017 * FStar_TypeChecker_Env.guard_t) ->
        ('Auu____1016 * 'Auu____1017 * FStar_TypeChecker_Env.guard_t)
  =
  fun env  ->
    fun uu____1039  ->
      match uu____1039 with
      | (te,kt,f) ->
          let uu____1049 = FStar_TypeChecker_Env.guard_form f  in
          (match uu____1049 with
           | FStar_TypeChecker_Common.Trivial  -> (te, kt, f)
           | FStar_TypeChecker_Common.NonTrivial f1 ->
               let uu____1057 =
                 FStar_TypeChecker_Err.unexpected_non_trivial_precondition_on_term
                   env f1
                  in
               let uu____1063 = FStar_TypeChecker_Env.get_range env  in
               FStar_Errors.raise_error uu____1057 uu____1063)
  
let (print_expected_ty : FStar_TypeChecker_Env.env -> unit) =
  fun env  ->
    let uu____1076 = FStar_TypeChecker_Env.expected_typ env  in
    match uu____1076 with
    | FStar_Pervasives_Native.None  ->
        FStar_Util.print_string "Expected type is None\n"
    | FStar_Pervasives_Native.Some t ->
        let uu____1081 = FStar_Syntax_Print.term_to_string t  in
        FStar_Util.print1 "Expected type is %s" uu____1081
  
let rec (get_pat_vars' :
  FStar_Syntax_Syntax.bv Prims.list ->
    Prims.bool ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  =
  fun all  ->
    fun andlist  ->
      fun pats  ->
        let pats1 = FStar_Syntax_Util.unmeta pats  in
        let uu____1123 = FStar_Syntax_Util.head_and_args pats1  in
        match uu____1123 with
        | (head1,args) ->
            let uu____1168 =
              let uu____1183 =
                let uu____1184 = FStar_Syntax_Util.un_uinst head1  in
                uu____1184.FStar_Syntax_Syntax.n  in
              (uu____1183, args)  in
            (match uu____1168 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1200) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 ->
                 if andlist
                 then FStar_Util.as_set all FStar_Syntax_Syntax.order_bv
                 else FStar_Util.new_set FStar_Syntax_Syntax.order_bv
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1227,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1228))::(hd1,FStar_Pervasives_Native.None
                                                                 )::(tl1,FStar_Pervasives_Native.None
                                                                    )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let hdvs = get_pat_vars' all false hd1  in
                 let tlvs = get_pat_vars' all andlist tl1  in
                 if andlist
                 then FStar_Util.set_intersect hdvs tlvs
                 else FStar_Util.set_union hdvs tlvs
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____1305,FStar_Pervasives_Native.Some
                    (FStar_Syntax_Syntax.Implicit uu____1306))::(pat,FStar_Pervasives_Native.None
                                                                 )::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> FStar_Syntax_Free.names pat
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> get_pat_vars' all true subpats
             | uu____1390 -> FStar_Util.new_set FStar_Syntax_Syntax.order_bv)

and (get_pat_vars :
  FStar_Syntax_Syntax.bv Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set)
  = fun all  -> fun pats  -> get_pat_vars' all false pats

let check_pat_fvs :
  'Auu____1421 .
    FStar_Range.range ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv * 'Auu____1421) Prims.list -> unit
  =
  fun rng  ->
    fun env  ->
      fun pats  ->
        fun bs  ->
          let pat_vars =
            let uu____1457 = FStar_List.map FStar_Pervasives_Native.fst bs
               in
            let uu____1464 =
              FStar_TypeChecker_Normalize.normalize
                [FStar_TypeChecker_Env.Beta] env pats
               in
            get_pat_vars uu____1457 uu____1464  in
          let uu____1465 =
            FStar_All.pipe_right bs
              (FStar_Util.find_opt
                 (fun uu____1492  ->
                    match uu____1492 with
                    | (b,uu____1499) ->
                        let uu____1500 = FStar_Util.set_mem b pat_vars  in
                        Prims.op_Negation uu____1500))
             in
          match uu____1465 with
          | FStar_Pervasives_Native.None  -> ()
          | FStar_Pervasives_Native.Some (x,uu____1507) ->
              let uu____1512 =
                let uu____1518 =
                  let uu____1520 = FStar_Syntax_Print.bv_to_string x  in
                  FStar_Util.format1
                    "Pattern misses at least one bound variable: %s"
                    uu____1520
                   in
                (FStar_Errors.Warning_SMTPatternIllFormed, uu____1518)  in
              FStar_Errors.log_issue rng uu____1512
  
let (check_no_smt_theory_symbols :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> unit) =
  fun en  ->
    fun t  ->
      let rec pat_terms t1 =
        let t2 = FStar_Syntax_Util.unmeta t1  in
        let uu____1546 = FStar_Syntax_Util.head_and_args t2  in
        match uu____1546 with
        | (head1,args) ->
            let uu____1591 =
              let uu____1606 =
                let uu____1607 = FStar_Syntax_Util.un_uinst head1  in
                uu____1607.FStar_Syntax_Syntax.n  in
              (uu____1606, args)  in
            (match uu____1591 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,uu____1623) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid
                 -> []
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1645::(hd1,uu____1647)::(tl1,uu____1649)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
                 ->
                 let uu____1716 = pat_terms hd1  in
                 let uu____1719 = pat_terms tl1  in
                 FStar_List.append uu____1716 uu____1719
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____1723::(pat,uu____1725)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> [pat]
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(subpats,FStar_Pervasives_Native.None )::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatOr_lid
                 -> pat_terms subpats
             | uu____1810 -> [])
         in
      let rec aux t1 =
        let uu____1835 =
          let uu____1836 = FStar_Syntax_Subst.compress t1  in
          uu____1836.FStar_Syntax_Syntax.n  in
        match uu____1835 with
        | FStar_Syntax_Syntax.Tm_bvar uu____1841 -> []
        | FStar_Syntax_Syntax.Tm_name uu____1842 -> []
        | FStar_Syntax_Syntax.Tm_type uu____1843 -> []
        | FStar_Syntax_Syntax.Tm_uvar uu____1844 -> []
        | FStar_Syntax_Syntax.Tm_lazy uu____1857 -> []
        | FStar_Syntax_Syntax.Tm_unknown  -> []
        | FStar_Syntax_Syntax.Tm_constant uu____1858 -> [t1]
        | FStar_Syntax_Syntax.Tm_abs uu____1859 -> [t1]
        | FStar_Syntax_Syntax.Tm_arrow uu____1878 -> [t1]
        | FStar_Syntax_Syntax.Tm_refine uu____1893 -> [t1]
        | FStar_Syntax_Syntax.Tm_match uu____1900 -> [t1]
        | FStar_Syntax_Syntax.Tm_let uu____1923 -> [t1]
        | FStar_Syntax_Syntax.Tm_delayed uu____1937 -> [t1]
        | FStar_Syntax_Syntax.Tm_quoted uu____1960 -> [t1]
        | FStar_Syntax_Syntax.Tm_fvar fv ->
            let uu____1968 =
              FStar_TypeChecker_Env.fv_has_attr en fv
                FStar_Parser_Const.smt_theory_symbol_attr_lid
               in
            if uu____1968 then [t1] else []
        | FStar_Syntax_Syntax.Tm_app (t2,args) ->
            let uu____2001 = aux t2  in
            FStar_List.fold_left
              (fun acc  ->
                 fun uu____2018  ->
                   match uu____2018 with
                   | (t3,uu____2030) ->
                       let uu____2035 = aux t3  in
                       FStar_List.append acc uu____2035) uu____2001 args
        | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____2039,uu____2040) ->
            aux t2
        | FStar_Syntax_Syntax.Tm_uinst (t2,uu____2082) -> aux t2
        | FStar_Syntax_Syntax.Tm_meta (t2,uu____2088) -> aux t2  in
      let tlist =
        let uu____2096 = FStar_All.pipe_right t pat_terms  in
        FStar_All.pipe_right uu____2096 (FStar_List.collect aux)  in
      if (FStar_List.length tlist) = Prims.int_zero
      then ()
      else
        (let msg =
           FStar_List.fold_left
             (fun s  ->
                fun t1  ->
                  let uu____2119 =
                    let uu____2121 = FStar_Syntax_Print.term_to_string t1  in
                    Prims.op_Hat " " uu____2121  in
                  Prims.op_Hat s uu____2119) "" tlist
            in
         let uu____2125 =
           let uu____2131 =
             FStar_Util.format1
               "Pattern uses these theory symbols or terms that should not be in an smt pattern: %s"
               msg
              in
           (FStar_Errors.Warning_SMTPatternIllFormed, uu____2131)  in
         FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu____2125)
  
let check_smt_pat :
  'Auu____2146 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.bv * 'Auu____2146) Prims.list ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> unit
  =
  fun env  ->
    fun t  ->
      fun bs  ->
        fun c  ->
          let uu____2187 = FStar_Syntax_Util.is_smt_lemma t  in
          if uu____2187
          then
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Comp
                { FStar_Syntax_Syntax.comp_univs = uu____2190;
                  FStar_Syntax_Syntax.effect_name = uu____2191;
                  FStar_Syntax_Syntax.result_typ = uu____2192;
                  FStar_Syntax_Syntax.effect_args =
                    _pre::_post::(pats,uu____2196)::[];
                  FStar_Syntax_Syntax.flags = uu____2197;_}
                ->
                (check_pat_fvs t.FStar_Syntax_Syntax.pos env pats bs;
                 check_no_smt_theory_symbols env pats)
            | uu____2259 -> failwith "Impossible"
          else ()
  
let (guard_letrecs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ *
          FStar_Syntax_Syntax.univ_names) Prims.list)
  =
  fun env  ->
    fun actuals  ->
      fun expected_c  ->
        match env.FStar_TypeChecker_Env.letrecs with
        | [] -> []
        | letrecs ->
            let r = FStar_TypeChecker_Env.get_range env  in
            let env1 =
              let uu___369_2322 = env  in
              {
                FStar_TypeChecker_Env.solver =
                  (uu___369_2322.FStar_TypeChecker_Env.solver);
                FStar_TypeChecker_Env.range =
                  (uu___369_2322.FStar_TypeChecker_Env.range);
                FStar_TypeChecker_Env.curmodule =
                  (uu___369_2322.FStar_TypeChecker_Env.curmodule);
                FStar_TypeChecker_Env.gamma =
                  (uu___369_2322.FStar_TypeChecker_Env.gamma);
                FStar_TypeChecker_Env.gamma_sig =
                  (uu___369_2322.FStar_TypeChecker_Env.gamma_sig);
                FStar_TypeChecker_Env.gamma_cache =
                  (uu___369_2322.FStar_TypeChecker_Env.gamma_cache);
                FStar_TypeChecker_Env.modules =
                  (uu___369_2322.FStar_TypeChecker_Env.modules);
                FStar_TypeChecker_Env.expected_typ =
                  (uu___369_2322.FStar_TypeChecker_Env.expected_typ);
                FStar_TypeChecker_Env.sigtab =
                  (uu___369_2322.FStar_TypeChecker_Env.sigtab);
                FStar_TypeChecker_Env.attrtab =
                  (uu___369_2322.FStar_TypeChecker_Env.attrtab);
                FStar_TypeChecker_Env.is_pattern =
                  (uu___369_2322.FStar_TypeChecker_Env.is_pattern);
                FStar_TypeChecker_Env.instantiate_imp =
                  (uu___369_2322.FStar_TypeChecker_Env.instantiate_imp);
                FStar_TypeChecker_Env.effects =
                  (uu___369_2322.FStar_TypeChecker_Env.effects);
                FStar_TypeChecker_Env.generalize =
                  (uu___369_2322.FStar_TypeChecker_Env.generalize);
                FStar_TypeChecker_Env.letrecs = [];
                FStar_TypeChecker_Env.top_level =
                  (uu___369_2322.FStar_TypeChecker_Env.top_level);
                FStar_TypeChecker_Env.check_uvars =
                  (uu___369_2322.FStar_TypeChecker_Env.check_uvars);
                FStar_TypeChecker_Env.use_eq =
                  (uu___369_2322.FStar_TypeChecker_Env.use_eq);
                FStar_TypeChecker_Env.is_iface =
                  (uu___369_2322.FStar_TypeChecker_Env.is_iface);
                FStar_TypeChecker_Env.admit =
                  (uu___369_2322.FStar_TypeChecker_Env.admit);
                FStar_TypeChecker_Env.lax =
                  (uu___369_2322.FStar_TypeChecker_Env.lax);
                FStar_TypeChecker_Env.lax_universes =
                  (uu___369_2322.FStar_TypeChecker_Env.lax_universes);
                FStar_TypeChecker_Env.phase1 =
                  (uu___369_2322.FStar_TypeChecker_Env.phase1);
                FStar_TypeChecker_Env.failhard =
                  (uu___369_2322.FStar_TypeChecker_Env.failhard);
                FStar_TypeChecker_Env.nosynth =
                  (uu___369_2322.FStar_TypeChecker_Env.nosynth);
                FStar_TypeChecker_Env.uvar_subtyping =
                  (uu___369_2322.FStar_TypeChecker_Env.uvar_subtyping);
                FStar_TypeChecker_Env.tc_term =
                  (uu___369_2322.FStar_TypeChecker_Env.tc_term);
                FStar_TypeChecker_Env.type_of =
                  (uu___369_2322.FStar_TypeChecker_Env.type_of);
                FStar_TypeChecker_Env.universe_of =
                  (uu___369_2322.FStar_TypeChecker_Env.universe_of);
                FStar_TypeChecker_Env.check_type_of =
                  (uu___369_2322.FStar_TypeChecker_Env.check_type_of);
                FStar_TypeChecker_Env.use_bv_sorts =
                  (uu___369_2322.FStar_TypeChecker_Env.use_bv_sorts);
                FStar_TypeChecker_Env.qtbl_name_and_index =
                  (uu___369_2322.FStar_TypeChecker_Env.qtbl_name_and_index);
                FStar_TypeChecker_Env.normalized_eff_names =
                  (uu___369_2322.FStar_TypeChecker_Env.normalized_eff_names);
                FStar_TypeChecker_Env.fv_delta_depths =
                  (uu___369_2322.FStar_TypeChecker_Env.fv_delta_depths);
                FStar_TypeChecker_Env.proof_ns =
                  (uu___369_2322.FStar_TypeChecker_Env.proof_ns);
                FStar_TypeChecker_Env.synth_hook =
                  (uu___369_2322.FStar_TypeChecker_Env.synth_hook);
                FStar_TypeChecker_Env.splice =
                  (uu___369_2322.FStar_TypeChecker_Env.splice);
                FStar_TypeChecker_Env.postprocess =
                  (uu___369_2322.FStar_TypeChecker_Env.postprocess);
                FStar_TypeChecker_Env.is_native_tactic =
                  (uu___369_2322.FStar_TypeChecker_Env.is_native_tactic);
                FStar_TypeChecker_Env.identifier_info =
                  (uu___369_2322.FStar_TypeChecker_Env.identifier_info);
                FStar_TypeChecker_Env.tc_hooks =
                  (uu___369_2322.FStar_TypeChecker_Env.tc_hooks);
                FStar_TypeChecker_Env.dsenv =
                  (uu___369_2322.FStar_TypeChecker_Env.dsenv);
                FStar_TypeChecker_Env.nbe =
                  (uu___369_2322.FStar_TypeChecker_Env.nbe);
                FStar_TypeChecker_Env.strict_args_tab =
                  (uu___369_2322.FStar_TypeChecker_Env.strict_args_tab)
              }  in
            let precedes =
              FStar_TypeChecker_Util.fvar_const env1
                FStar_Parser_Const.precedes_lid
               in
            let decreases_clause bs c =
              (let uu____2348 =
                 FStar_TypeChecker_Env.debug env1 FStar_Options.Low  in
               if uu____2348
               then
                 let uu____2351 =
                   FStar_Syntax_Print.binders_to_string ", " bs  in
                 let uu____2354 = FStar_Syntax_Print.comp_to_string c  in
                 FStar_Util.print2
                   "Building a decreases clause over (%s) and %s\n"
                   uu____2351 uu____2354
               else ());
              (let filter_types_and_functions bs1 =
                 FStar_All.pipe_right bs1
                   (FStar_List.collect
                      (fun uu____2388  ->
                         match uu____2388 with
                         | (b,uu____2398) ->
                             let t =
                               let uu____2404 =
                                 FStar_Syntax_Util.unrefine
                                   b.FStar_Syntax_Syntax.sort
                                  in
                               FStar_TypeChecker_Normalize.unfold_whnf env1
                                 uu____2404
                                in
                             (match t.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_type uu____2407 -> []
                              | FStar_Syntax_Syntax.Tm_arrow uu____2408 -> []
                              | uu____2423 ->
                                  let uu____2424 =
                                    FStar_Syntax_Syntax.bv_to_name b  in
                                  [uu____2424])))
                  in
               let as_lex_list dec =
                 let uu____2437 = FStar_Syntax_Util.head_and_args dec  in
                 match uu____2437 with
                 | (head1,uu____2457) ->
                     (match head1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Tm_fvar fv when
                          FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.lexcons_lid
                          -> dec
                      | uu____2485 -> mk_lex_list [dec])
                  in
               let cflags = FStar_Syntax_Util.comp_flags c  in
               let uu____2493 =
                 FStar_All.pipe_right cflags
                   (FStar_List.tryFind
                      (fun uu___1_2502  ->
                         match uu___1_2502 with
                         | FStar_Syntax_Syntax.DECREASES uu____2504 -> true
                         | uu____2508 -> false))
                  in
               match uu____2493 with
               | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                   dec) -> as_lex_list dec
               | uu____2515 ->
                   let xs =
                     FStar_All.pipe_right bs filter_types_and_functions  in
                   (match xs with | x::[] -> x | uu____2536 -> mk_lex_list xs))
               in
            let previous_dec = decreases_clause actuals expected_c  in
            let guard_one_letrec uu____2565 =
              match uu____2565 with
              | (l,t,u_names) ->
                  let uu____2589 =
                    let uu____2590 = FStar_Syntax_Subst.compress t  in
                    uu____2590.FStar_Syntax_Syntax.n  in
                  (match uu____2589 with
                   | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                       let formals1 =
                         FStar_All.pipe_right formals
                           (FStar_List.map
                              (fun uu____2649  ->
                                 match uu____2649 with
                                 | (x,imp) ->
                                     let uu____2668 =
                                       FStar_Syntax_Syntax.is_null_bv x  in
                                     if uu____2668
                                     then
                                       let uu____2677 =
                                         let uu____2678 =
                                           let uu____2681 =
                                             FStar_Syntax_Syntax.range_of_bv
                                               x
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____2681
                                            in
                                         FStar_Syntax_Syntax.new_bv
                                           uu____2678
                                           x.FStar_Syntax_Syntax.sort
                                          in
                                       (uu____2677, imp)
                                     else (x, imp)))
                          in
                       let uu____2688 =
                         FStar_Syntax_Subst.open_comp formals1 c  in
                       (match uu____2688 with
                        | (formals2,c1) ->
                            let dec = decreases_clause formals2 c1  in
                            let precedes1 =
                              let uu____2709 =
                                let uu____2714 =
                                  let uu____2715 =
                                    FStar_Syntax_Syntax.as_arg dec  in
                                  let uu____2724 =
                                    let uu____2735 =
                                      FStar_Syntax_Syntax.as_arg previous_dec
                                       in
                                    [uu____2735]  in
                                  uu____2715 :: uu____2724  in
                                FStar_Syntax_Syntax.mk_Tm_app precedes
                                  uu____2714
                                 in
                              uu____2709 FStar_Pervasives_Native.None r  in
                            let precedes2 =
                              FStar_TypeChecker_Util.label
                                "Could not prove termination of this recursive call"
                                r precedes1
                               in
                            let uu____2770 = FStar_Util.prefix formals2  in
                            (match uu____2770 with
                             | (bs,(last1,imp)) ->
                                 let last2 =
                                   let uu___436_2833 = last1  in
                                   let uu____2834 =
                                     FStar_Syntax_Util.refine last1 precedes2
                                      in
                                   {
                                     FStar_Syntax_Syntax.ppname =
                                       (uu___436_2833.FStar_Syntax_Syntax.ppname);
                                     FStar_Syntax_Syntax.index =
                                       (uu___436_2833.FStar_Syntax_Syntax.index);
                                     FStar_Syntax_Syntax.sort = uu____2834
                                   }  in
                                 let refined_formals =
                                   FStar_List.append bs [(last2, imp)]  in
                                 let t' =
                                   FStar_Syntax_Util.arrow refined_formals c1
                                    in
                                 ((let uu____2870 =
                                     FStar_TypeChecker_Env.debug env1
                                       FStar_Options.Low
                                      in
                                   if uu____2870
                                   then
                                     let uu____2873 =
                                       FStar_Syntax_Print.lbname_to_string l
                                        in
                                     let uu____2875 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     let uu____2877 =
                                       FStar_Syntax_Print.term_to_string t'
                                        in
                                     FStar_Util.print3
                                       "Refined let rec %s\n\tfrom type %s\n\tto type %s\n"
                                       uu____2873 uu____2875 uu____2877
                                   else ());
                                  (l, t', u_names))))
                   | uu____2884 ->
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_ExpectedArrowAnnotatedType,
                           "Annotated type of 'let rec' must be an arrow")
                         t.FStar_Syntax_Syntax.pos)
               in
            FStar_All.pipe_right letrecs (FStar_List.map guard_one_letrec)
  
let (wrap_guard_with_tactic_opt :
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.guard_t -> FStar_TypeChecker_Env.guard_t)
  =
  fun topt  ->
    fun g  ->
      match topt with
      | FStar_Pervasives_Native.None  -> g
      | FStar_Pervasives_Native.Some tactic ->
          FStar_TypeChecker_Env.always_map_guard g
            (fun g1  ->
               let uu____2948 =
                 FStar_Syntax_Util.mk_squash FStar_Syntax_Syntax.U_zero g1
                  in
               FStar_TypeChecker_Common.mk_by_tactic tactic uu____2948)
  
let rec (tc_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____3561 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3561
       then
         let uu____3564 =
           let uu____3566 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3566  in
         let uu____3568 = FStar_Syntax_Print.term_to_string e  in
         let uu____3570 =
           let uu____3572 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3572  in
         FStar_Util.print3 "(%s) Starting tc_term of %s (%s) {\n" uu____3564
           uu____3568 uu____3570
       else ());
      (let uu____3576 =
         FStar_Util.record_time
           (fun uu____3595  ->
              tc_maybe_toplevel_term
                (let uu___455_3598 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___455_3598.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___455_3598.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___455_3598.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___455_3598.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___455_3598.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___455_3598.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___455_3598.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___455_3598.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___455_3598.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___455_3598.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___455_3598.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___455_3598.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___455_3598.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___455_3598.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___455_3598.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___455_3598.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___455_3598.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___455_3598.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___455_3598.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___455_3598.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___455_3598.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___455_3598.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___455_3598.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___455_3598.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___455_3598.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___455_3598.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___455_3598.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___455_3598.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___455_3598.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___455_3598.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___455_3598.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___455_3598.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___455_3598.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___455_3598.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___455_3598.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___455_3598.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___455_3598.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___455_3598.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___455_3598.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___455_3598.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___455_3598.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___455_3598.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___455_3598.FStar_TypeChecker_Env.strict_args_tab)
                 }) e)
          in
       match uu____3576 with
       | (r,ms) ->
           ((let uu____3623 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3623
             then
               ((let uu____3627 =
                   let uu____3629 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3629
                    in
                 let uu____3631 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3633 =
                   let uu____3635 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3635  in
                 let uu____3636 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3627 uu____3631 uu____3633 uu____3636);
                (let uu____3639 = r  in
                 match uu____3639 with
                 | (e1,uu____3647,uu____3648) ->
                     let uu____3649 =
                       let uu____3651 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3651
                        in
                     let uu____3653 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____3655 =
                       let uu____3657 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____3657  in
                     FStar_Util.print3 "(%s) Result is: %s (%s)\n" uu____3649
                       uu____3653 uu____3655))
             else ());
            r))

and (tc_maybe_toplevel_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 =
        if e.FStar_Syntax_Syntax.pos = FStar_Range.dummyRange
        then env
        else FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos
         in
      let top = FStar_Syntax_Subst.compress e  in
      (let uu____3675 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____3675
       then
         let uu____3678 =
           let uu____3680 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3680  in
         let uu____3682 = FStar_Syntax_Print.tag_of_term top  in
         let uu____3684 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3678 uu____3682
           uu____3684
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3695 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3725 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3732 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3745 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3746 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3747 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3748 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3749 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3768 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3783 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3790 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_3806 =
             match uu___2_3806 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3812 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3828 =
                 let uu____3829 = FStar_Syntax_Subst.compress t  in
                 uu____3829.FStar_Syntax_Syntax.n  in
               match uu____3828 with
               | FStar_Syntax_Syntax.Tm_name uu____3833 -> true
               | uu____3835 -> false  in
             FStar_Util.for_some
               (fun uu____3845  ->
                  match uu____3845 with
                  | (uu____3851,t) ->
                      let uu____3853 = is_name1 t  in
                      Prims.op_Negation uu____3853)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____3872  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____3915  ->
                       match uu____3915 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___528_3944 = qi  in
                  let uu____3945 =
                    FStar_List.map
                      (fun uu____3973  ->
                         match uu____3973 with
                         | ((bv,uu____3989),bv') ->
                             let uu____4001 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4001)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___528_3944.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3945
                  }  in
                let nq =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                let e1 =
                  FStar_List.fold_left
                    (fun t  ->
                       fun lb  ->
                         let uu____4013 =
                           let uu____4020 =
                             let uu____4021 =
                               let uu____4035 =
                                 let uu____4038 =
                                   let uu____4039 =
                                     let uu____4046 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4046
                                      in
                                   [uu____4039]  in
                                 FStar_Syntax_Subst.close uu____4038 t  in
                               ((false, [lb]), uu____4035)  in
                             FStar_Syntax_Syntax.Tm_let uu____4021  in
                           FStar_Syntax_Syntax.mk uu____4020  in
                         uu____4013 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4082 =
                  FStar_List.fold_right
                    (fun uu____4118  ->
                       fun uu____4119  ->
                         match (uu____4118, uu____4119) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4188 = tc_term env_tm tm  in
                             (match uu____4188 with
                              | (tm1,uu____4206,g) ->
                                  let uu____4208 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4208))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4082 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___556_4250 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___556_4250.FStar_Syntax_Syntax.qkind);
                         FStar_Syntax_Syntax.antiquotes =
                           (FStar_List.rev aqs_rev)
                       }  in
                     let tm =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_quoted (qt, qi1))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     value_check_expected_typ env1 tm
                       (FStar_Util.Inl FStar_Syntax_Syntax.t_term) guard)
            | FStar_Syntax_Syntax.Quote_dynamic  ->
                let c =
                  FStar_Syntax_Syntax.mk_Comp
                    {
                      FStar_Syntax_Syntax.comp_univs =
                        [FStar_Syntax_Syntax.U_zero];
                      FStar_Syntax_Syntax.effect_name =
                        FStar_Parser_Const.effect_Tac_lid;
                      FStar_Syntax_Syntax.result_typ =
                        FStar_Syntax_Syntax.t_term;
                      FStar_Syntax_Syntax.effect_args = [];
                      FStar_Syntax_Syntax.flags =
                        [FStar_Syntax_Syntax.SOMETRIVIAL;
                        FStar_Syntax_Syntax.TRIVIAL_POSTCONDITION]
                    }
                   in
                let uu____4269 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4269 with
                 | (env',uu____4283) ->
                     let uu____4288 =
                       tc_term
                         (let uu___565_4297 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___565_4297.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___565_4297.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___565_4297.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___565_4297.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___565_4297.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___565_4297.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___565_4297.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___565_4297.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___565_4297.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___565_4297.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___565_4297.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___565_4297.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___565_4297.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___565_4297.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___565_4297.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___565_4297.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___565_4297.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___565_4297.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___565_4297.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___565_4297.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___565_4297.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___565_4297.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___565_4297.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___565_4297.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___565_4297.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___565_4297.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___565_4297.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___565_4297.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___565_4297.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___565_4297.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___565_4297.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___565_4297.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___565_4297.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___565_4297.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___565_4297.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___565_4297.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___565_4297.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___565_4297.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___565_4297.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___565_4297.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___565_4297.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___565_4297.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___565_4297.FStar_TypeChecker_Env.strict_args_tab)
                          }) qt
                        in
                     (match uu____4288 with
                      | (qt1,uu____4306,uu____4307) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4313 =
                            let uu____4320 =
                              let uu____4325 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4325  in
                            value_check_expected_typ env1 top uu____4320
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4313 with
                           | (t1,lc,g) ->
                               let t2 =
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_meta
                                      (t1,
                                        (FStar_Syntax_Syntax.Meta_monadic_lift
                                           (FStar_Parser_Const.effect_PURE_lid,
                                             FStar_Parser_Const.effect_TAC_lid,
                                             FStar_Syntax_Syntax.t_term))))
                                   FStar_Pervasives_Native.None
                                   t1.FStar_Syntax_Syntax.pos
                                  in
                               (t2, lc, g)))))
       | FStar_Syntax_Syntax.Tm_lazy
           { FStar_Syntax_Syntax.blob = uu____4342;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4343;
             FStar_Syntax_Syntax.ltyp = uu____4344;
             FStar_Syntax_Syntax.rng = uu____4345;_}
           ->
           let uu____4356 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4356
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4363 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4363 with
            | (e2,c,g) ->
                let g1 =
                  let uu___595_4380 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___595_4380.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___595_4380.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___595_4380.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4381 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4381, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats)) ->
           let uu____4423 = FStar_Syntax_Util.type_u ()  in
           (match uu____4423 with
            | (t,u) ->
                let uu____4436 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4436 with
                 | (e2,c,g) ->
                     let uu____4452 =
                       let uu____4469 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4469 with
                       | (env2,uu____4493) -> tc_smt_pats env2 pats  in
                     (match uu____4452 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___618_4531 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___618_4531.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___618_4531.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___618_4531.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____4532 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4551 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4532, c, uu____4551))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4557 =
             let uu____4558 = FStar_Syntax_Subst.compress e1  in
             uu____4558.FStar_Syntax_Syntax.n  in
           (match uu____4557 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4567,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4569;
                               FStar_Syntax_Syntax.lbtyp = uu____4570;
                               FStar_Syntax_Syntax.lbeff = uu____4571;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4573;
                               FStar_Syntax_Syntax.lbpos = uu____4574;_}::[]),e2)
                ->
                let uu____4605 =
                  let uu____4612 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4612 e11  in
                (match uu____4605 with
                 | (e12,c1,g1) ->
                     let uu____4622 = tc_term env1 e2  in
                     (match uu____4622 with
                      | (e21,c2,g2) ->
                          let c =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e12.FStar_Syntax_Syntax.pos env1
                              (FStar_Pervasives_Native.Some e12) c1 e21
                              (FStar_Pervasives_Native.None, c2)
                             in
                          let e13 =
                            FStar_TypeChecker_Util.maybe_lift env1 e12
                              c1.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ
                             in
                          let e22 =
                            FStar_TypeChecker_Util.maybe_lift env1 e21
                              c2.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.eff_name
                              c2.FStar_TypeChecker_Common.res_typ
                             in
                          let attrs =
                            let uu____4646 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____4646
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____4656 =
                              let uu____4663 =
                                let uu____4664 =
                                  let uu____4678 =
                                    let uu____4686 =
                                      let uu____4689 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____4689]  in
                                    (false, uu____4686)  in
                                  (uu____4678, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____4664  in
                              FStar_Syntax_Syntax.mk uu____4663  in
                            uu____4656 FStar_Pervasives_Native.None
                              e1.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env1 e3
                              c.FStar_TypeChecker_Common.eff_name
                              c.FStar_TypeChecker_Common.res_typ
                             in
                          let e5 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e4,
                                   (FStar_Syntax_Syntax.Meta_desugared
                                      FStar_Syntax_Syntax.Sequence)))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4713 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____4713)))
            | uu____4714 ->
                let uu____4715 = tc_term env1 e1  in
                (match uu____4715 with
                 | (e2,c,g) ->
                     let e3 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_meta
                            (e2,
                              (FStar_Syntax_Syntax.Meta_desugared
                                 FStar_Syntax_Syntax.Sequence)))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     (e3, c, g)))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____4737) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____4749) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____4768 = tc_term env1 e1  in
           (match uu____4768 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____4792) ->
           let uu____4839 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4839 with
            | (env0,uu____4853) ->
                let uu____4858 = tc_comp env0 expected_c  in
                (match uu____4858 with
                 | (expected_c1,uu____4872,g) ->
                     let uu____4874 =
                       let uu____4881 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____4881 e1  in
                     (match uu____4874 with
                      | (e2,c',g') ->
                          let uu____4891 =
                            let uu____4902 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____4902 with
                            | (c'1,g_c') ->
                                let uu____4919 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____4919 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____4939 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____4939))
                             in
                          (match uu____4891 with
                           | (e3,expected_c2,g'') ->
                               let uu____4961 = tc_tactic_opt env0 topt  in
                               (match uu____4961 with
                                | (topt1,gtac) ->
                                    let e4 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_ascribed
                                           (e3,
                                             ((FStar_Util.Inr expected_c2),
                                               topt1),
                                             (FStar_Pervasives_Native.Some
                                                (FStar_Syntax_Util.comp_effect_name
                                                   expected_c2))))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let lc =
                                      FStar_TypeChecker_Common.lcomp_of_comp
                                        expected_c2
                                       in
                                    let f =
                                      let uu____5021 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5021
                                       in
                                    let uu____5022 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____5022 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____5039 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5039
                                            in
                                         let uu____5040 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____5040)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____5044) ->
           let uu____5091 = FStar_Syntax_Util.type_u ()  in
           (match uu____5091 with
            | (k,u) ->
                let uu____5104 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____5104 with
                 | (t1,uu____5118,f) ->
                     let uu____5120 = tc_tactic_opt env1 topt  in
                     (match uu____5120 with
                      | (topt1,gtac) ->
                          let uu____5139 =
                            let uu____5146 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____5146 e1  in
                          (match uu____5139 with
                           | (e2,c,g) ->
                               let uu____5156 =
                                 let uu____5161 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5167  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5161 e2 c f
                                  in
                               (match uu____5156 with
                                | (c1,f1) ->
                                    let uu____5177 =
                                      let uu____5184 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____5184
                                        c1
                                       in
                                    (match uu____5177 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____5231 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5231
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____5233 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____5233)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5234;
              FStar_Syntax_Syntax.vars = uu____5235;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5314 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5314 with
            | (unary_op1,uu____5338) ->
                let head1 =
                  let uu____5366 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5366
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____5414;
              FStar_Syntax_Syntax.vars = uu____5415;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5494 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5494 with
            | (unary_op1,uu____5518) ->
                let head1 =
                  let uu____5546 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5546
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect uu____5594);
              FStar_Syntax_Syntax.pos = uu____5595;
              FStar_Syntax_Syntax.vars = uu____5596;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5675 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5675 with
            | (unary_op1,uu____5699) ->
                let head1 =
                  let uu____5727 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5727
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____5775;
              FStar_Syntax_Syntax.vars = uu____5776;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5872 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5872 with
            | (unary_op1,uu____5896) ->
                let head1 =
                  let uu____5924 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5924
                   in
                let t =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                tc_term env1 t)
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5980;
              FStar_Syntax_Syntax.vars = uu____5981;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____6019 =
             let uu____6026 =
               let uu____6027 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6027  in
             tc_term uu____6026 e1  in
           (match uu____6019 with
            | (e2,c,g) ->
                let uu____6051 = FStar_Syntax_Util.head_and_args top  in
                (match uu____6051 with
                 | (head1,uu____6075) ->
                     let uu____6100 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____6133 =
                       let uu____6134 =
                         let uu____6135 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____6135  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____6134
                        in
                     (uu____6100, uu____6133, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6136;
              FStar_Syntax_Syntax.vars = uu____6137;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____6190 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6190 with
            | (head1,uu____6214) ->
                let env' =
                  let uu____6240 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6240  in
                let uu____6241 = tc_term env' r  in
                (match uu____6241 with
                 | (er,uu____6255,gr) ->
                     let uu____6257 = tc_term env1 t  in
                     (match uu____6257 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____6274 =
                            let uu____6275 =
                              let uu____6280 =
                                let uu____6281 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____6290 =
                                  let uu____6301 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____6301]  in
                                uu____6281 :: uu____6290  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6280
                               in
                            uu____6275 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____6274, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6334;
              FStar_Syntax_Syntax.vars = uu____6335;_},uu____6336)
           ->
           let uu____6361 =
             let uu____6367 =
               let uu____6369 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6369  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6367)  in
           FStar_Errors.raise_error uu____6361 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6379;
              FStar_Syntax_Syntax.vars = uu____6380;_},uu____6381)
           ->
           let uu____6406 =
             let uu____6412 =
               let uu____6414 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6414  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6412)  in
           FStar_Errors.raise_error uu____6406 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6424;
              FStar_Syntax_Syntax.vars = uu____6425;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6472 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____6472 with
             | (env0,uu____6486) ->
                 let uu____6491 = tc_term env0 e1  in
                 (match uu____6491 with
                  | (e2,c,g) ->
                      let uu____6507 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____6507 with
                       | (reify_op,uu____6531) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____6557 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____6557 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____6572 =
                                    let uu____6574 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____6574  in
                                  if uu____6572
                                  then
                                    let uu____6577 =
                                      let uu____6583 =
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          ef.FStar_Ident.str
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____6583)
                                       in
                                    FStar_Errors.raise_error uu____6577
                                      e2.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let repr =
                                    FStar_TypeChecker_Env.reify_comp env1 c1
                                      u_c
                                     in
                                  let e3 =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         (reify_op, [(e2, aqual)]))
                                      FStar_Pervasives_Native.None
                                      top.FStar_Syntax_Syntax.pos
                                     in
                                  let c2 =
                                    let uu____6626 =
                                      FStar_TypeChecker_Env.is_total_effect
                                        env1 ef
                                       in
                                    if uu____6626
                                    then
                                      let uu____6629 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____6629
                                        FStar_TypeChecker_Common.lcomp_of_comp
                                    else
                                      (let ct =
                                         {
                                           FStar_Syntax_Syntax.comp_univs =
                                             [u_c];
                                           FStar_Syntax_Syntax.effect_name =
                                             FStar_Parser_Const.effect_Dv_lid;
                                           FStar_Syntax_Syntax.result_typ =
                                             repr;
                                           FStar_Syntax_Syntax.effect_args =
                                             [];
                                           FStar_Syntax_Syntax.flags = []
                                         }  in
                                       let uu____6641 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____6641
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____6642 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____6642 with
                                  | (e4,c3,g') ->
                                      let uu____6658 =
                                        let uu____6659 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____6659
                                         in
                                      (e4, c3, uu____6658))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6661;
              FStar_Syntax_Syntax.vars = uu____6662;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6710 =
               let uu____6712 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____6712  in
             if uu____6710
             then
               let uu____6715 =
                 let uu____6721 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6721)  in
               FStar_Errors.raise_error uu____6715 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6727 = FStar_Syntax_Util.head_and_args top  in
             match uu____6727 with
             | (reflect_op,uu____6751) ->
                 let uu____6776 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____6776 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____6816 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____6816 with
                       | (env_no_ex,topt) ->
                           let uu____6835 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed ed.FStar_Syntax_Syntax.repr
                                in
                             let t =
                               let uu____6851 =
                                 let uu____6858 =
                                   let uu____6859 =
                                     let uu____6876 =
                                       let uu____6887 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____6896 =
                                         let uu____6907 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____6907]  in
                                       uu____6887 :: uu____6896  in
                                     (repr, uu____6876)  in
                                   FStar_Syntax_Syntax.Tm_app uu____6859  in
                                 FStar_Syntax_Syntax.mk uu____6858  in
                               uu____6851 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6952 =
                               let uu____6959 =
                                 let uu____6960 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____6960
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____6959 t  in
                             match uu____6952 with
                             | (t1,uu____6986,g) ->
                                 let uu____6988 =
                                   let uu____6989 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____6989.FStar_Syntax_Syntax.n  in
                                 (match uu____6988 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____7002,(res,uu____7004)::(wp,uu____7006)::[])
                                      -> (t1, res, wp, g)
                                  | uu____7063 -> failwith "Impossible")
                              in
                           (match uu____6835 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____7089 =
                                  let uu____7096 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____7096 with
                                  | (e2,c,g) ->
                                      ((let uu____7113 =
                                          let uu____7115 =
                                            FStar_TypeChecker_Common.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____7115
                                           in
                                        if uu____7113
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____7138 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_TypeChecker_Common.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____7138 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____7149 =
                                                let uu____7159 =
                                                  let uu____7167 =
                                                    let uu____7169 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____7171 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_TypeChecker_Common.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____7169 uu____7171
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____7167,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____7159]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____7149);
                                             (let uu____7189 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____7189)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____7193 =
                                              let uu____7194 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____7194
                                               in
                                            (e2, uu____7193)))
                                   in
                                (match uu____7089 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____7210 =
                                         let uu____7211 =
                                           let uu____7212 =
                                             let uu____7213 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____7213]  in
                                           let uu____7214 =
                                             let uu____7225 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____7225]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____7212;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7214;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7211
                                          in
                                       FStar_All.pipe_right uu____7210
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____7285 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____7285 with
                                      | (e4,c1,g') ->
                                          let e5 =
                                            FStar_Syntax_Syntax.mk
                                              (FStar_Syntax_Syntax.Tm_meta
                                                 (e4,
                                                   (FStar_Syntax_Syntax.Meta_monadic
                                                      ((c1.FStar_TypeChecker_Common.eff_name),
                                                        (c1.FStar_TypeChecker_Common.res_typ)))))
                                              FStar_Pervasives_Native.None
                                              e4.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____7308 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____7308))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7347 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7347 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____7397,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____7398))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7451 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7451 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7526 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7736 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____7526 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____7855 =
               let uu____7856 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____7856 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____7855 instantiate_both  in
           ((let uu____7872 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____7872
             then
               let uu____7875 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____7877 = FStar_Syntax_Print.term_to_string top  in
               let uu____7879 =
                 let uu____7881 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____7881
                   (fun uu___3_7888  ->
                      match uu___3_7888 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7875
                 uu____7877 uu____7879
             else ());
            (let uu____7897 = tc_term (no_inst env2) head1  in
             match uu____7897 with
             | (head2,chead,g_head) ->
                 let uu____7913 =
                   let uu____7918 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____7918
                     (fun uu____7935  ->
                        match uu____7935 with
                        | (c,g) ->
                            let uu____7946 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____7946))
                    in
                 (match uu____7913 with
                  | (chead1,g_head1) ->
                      let uu____7955 =
                        let uu____7962 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____7965 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____7965))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head2)
                           in
                        if uu____7962
                        then
                          let uu____7974 =
                            let uu____7981 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head2 chead1
                              g_head1 args uu____7981
                             in
                          match uu____7974 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____7995 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head2 chead1 g_head1
                             args uu____7995)
                         in
                      (match uu____7955 with
                       | (e1,c,g) ->
                           let uu____8007 =
                             let uu____8014 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8014
                             then
                               let uu____8023 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8023 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8039 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8039, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8007 with
                            | (e2,c1,implicits) ->
                                ((let uu____8052 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8052
                                  then
                                    let uu____8055 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8055
                                  else ());
                                 (let uu____8060 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8060 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8079 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8079
                                        then
                                          let uu____8082 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8084 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8082 uu____8084
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____8127 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____8127 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____8147 = tc_term env12 e1  in
                (match uu____8147 with
                 | (e11,c1,g1) ->
                     let uu____8163 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8177 = FStar_Syntax_Util.type_u ()  in
                           (match uu____8177 with
                            | (k,uu____8189) ->
                                let uu____8190 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____8190 with
                                 | (res_t,uu____8211,g) ->
                                     let uu____8225 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____8226 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____8225, res_t, uu____8226)))
                        in
                     (match uu____8163 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____8237 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____8237
                            then
                              let uu____8240 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____8240
                            else ());
                           (let guard_x =
                              FStar_Syntax_Syntax.new_bv
                                (FStar_Pervasives_Native.Some
                                   (e11.FStar_Syntax_Syntax.pos))
                                c1.FStar_TypeChecker_Common.res_typ
                               in
                            let t_eqns =
                              FStar_All.pipe_right eqns
                                (FStar_List.map (tc_eqn guard_x env_branches))
                               in
                            let uu____8367 =
                              let uu____8372 =
                                FStar_List.fold_right
                                  (fun uu____8454  ->
                                     fun uu____8455  ->
                                       match (uu____8454, uu____8455) with
                                       | ((branch1,f,eff_label,cflags,c,g),
                                          (caccum,gaccum)) ->
                                           let uu____8700 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8700)) t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard)
                                 in
                              match uu____8372 with
                              | (cases,g) ->
                                  let uu____8805 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____8805, g)
                               in
                            match uu____8367 with
                            | (c_branches,g_branches) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches)
                                   in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____8947  ->
                                              match uu____8947 with
                                              | ((pat,wopt,br),uu____8992,eff_label,uu____8994,uu____8995,uu____8996)
                                                  ->
                                                  let uu____9033 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres.FStar_TypeChecker_Common.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____9033)))
                                       in
                                    let e2 =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_match
                                           (scrutinee, branches))
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let e3 =
                                      FStar_TypeChecker_Util.maybe_monadic
                                        env1 e2
                                        cres.FStar_TypeChecker_Common.eff_name
                                        cres.FStar_TypeChecker_Common.res_typ
                                       in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres.FStar_TypeChecker_Common.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres.FStar_TypeChecker_Common.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____9100 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1
                                      c1.FStar_TypeChecker_Common.eff_name
                                     in
                                  if uu____9100
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____9108 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____9108  in
                                     let lb =
                                       let uu____9112 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_TypeChecker_Common.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_TypeChecker_Common.res_typ
                                         uu____9112 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____9118 =
                                         let uu____9125 =
                                           let uu____9126 =
                                             let uu____9140 =
                                               let uu____9143 =
                                                 let uu____9144 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____9144]  in
                                               FStar_Syntax_Subst.close
                                                 uu____9143 e_match
                                                in
                                             ((false, [lb]), uu____9140)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____9126
                                            in
                                         FStar_Syntax_Syntax.mk uu____9125
                                          in
                                       uu____9118
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres.FStar_TypeChecker_Common.eff_name
                                       cres.FStar_TypeChecker_Common.res_typ)
                                   in
                                ((let uu____9177 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____9177
                                  then
                                    let uu____9180 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____9182 =
                                      FStar_TypeChecker_Common.lcomp_to_string
                                        cres
                                       in
                                    FStar_Util.print2 "(%s) comp type = %s\n"
                                      uu____9180 uu____9182
                                  else ());
                                 (let uu____9187 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres, uu____9187))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9188;
                FStar_Syntax_Syntax.lbunivs = uu____9189;
                FStar_Syntax_Syntax.lbtyp = uu____9190;
                FStar_Syntax_Syntax.lbeff = uu____9191;
                FStar_Syntax_Syntax.lbdef = uu____9192;
                FStar_Syntax_Syntax.lbattrs = uu____9193;
                FStar_Syntax_Syntax.lbpos = uu____9194;_}::[]),uu____9195)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9221),uu____9222) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9240;
                FStar_Syntax_Syntax.lbunivs = uu____9241;
                FStar_Syntax_Syntax.lbtyp = uu____9242;
                FStar_Syntax_Syntax.lbeff = uu____9243;
                FStar_Syntax_Syntax.lbdef = uu____9244;
                FStar_Syntax_Syntax.lbattrs = uu____9245;
                FStar_Syntax_Syntax.lbpos = uu____9246;_}::uu____9247),uu____9248)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9276),uu____9277) ->
           check_inner_let_rec env1 top)

and (tc_synth :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list ->
        FStar_Range.range ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun head1  ->
    fun env  ->
      fun args  ->
        fun rng  ->
          let uu____9311 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9350))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9391 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____9311 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____9424 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____9424 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____9428 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9428)
                 in
              let uu____9431 =
                let uu____9438 =
                  let uu____9439 =
                    let uu____9440 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9440
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9439  in
                tc_term uu____9438 typ  in
              (match uu____9431 with
               | (typ1,uu____9456,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9459 = tc_tactic env tau  in
                     match uu____9459 with
                     | (tau1,uu____9473,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1231_9478 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1231_9478.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1231_9478.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____9480 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____9480
                            then
                              let uu____9485 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____9485
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9491 =
                              let uu____9492 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____9492
                               in
                            (t, uu____9491,
                              FStar_TypeChecker_Env.trivial_guard)))))))

and (tc_tactic :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun tau  ->
      let env1 =
        let uu___1239_9496 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1239_9496.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1239_9496.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1239_9496.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1239_9496.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1239_9496.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1239_9496.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1239_9496.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1239_9496.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1239_9496.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1239_9496.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1239_9496.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1239_9496.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1239_9496.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1239_9496.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1239_9496.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1239_9496.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1239_9496.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1239_9496.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1239_9496.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1239_9496.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1239_9496.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1239_9496.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1239_9496.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1239_9496.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1239_9496.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1239_9496.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1239_9496.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1239_9496.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1239_9496.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1239_9496.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1239_9496.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1239_9496.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1239_9496.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1239_9496.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1239_9496.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1239_9496.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1239_9496.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1239_9496.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1239_9496.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1239_9496.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1239_9496.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1239_9496.FStar_TypeChecker_Env.nbe);
          FStar_TypeChecker_Env.strict_args_tab =
            (uu___1239_9496.FStar_TypeChecker_Env.strict_args_tab)
        }  in
      tc_check_tot_or_gtot_term env1 tau FStar_Syntax_Syntax.t_tactic_unit

and (tc_tactic_opt :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun topt  ->
      match topt with
      | FStar_Pervasives_Native.None  ->
          (FStar_Pervasives_Native.None, FStar_TypeChecker_Env.trivial_guard)
      | FStar_Pervasives_Native.Some tactic ->
          let uu____9519 = tc_tactic env tactic  in
          (match uu____9519 with
           | (tactic1,uu____9533,g) ->
               ((FStar_Pervasives_Native.Some tactic1), g))

and (tc_value :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let check_instantiated_fvar env1 v1 dc e1 t0 =
        let uu____9585 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____9585 with
        | (e2,t,implicits) ->
            let tc =
              let uu____9606 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____9606
              then FStar_Util.Inl t
              else
                (let uu____9615 =
                   let uu____9616 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____9616
                    in
                 FStar_Util.Inr uu____9615)
               in
            let is_data_ctor uu___4_9625 =
              match uu___4_9625 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9630) -> true
              | uu____9638 -> false  in
            let uu____9642 =
              (is_data_ctor dc) &&
                (let uu____9645 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____9645)
               in
            if uu____9642
            then
              let uu____9654 =
                let uu____9660 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9660)  in
              let uu____9664 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____9654 uu____9664
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9682 =
            let uu____9684 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9684
             in
          failwith uu____9682
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____9711 =
            let uu____9716 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____9716  in
          value_check_expected_typ env1 e uu____9711
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____9718 =
            let uu____9731 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____9731 with
            | FStar_Pervasives_Native.None  ->
                let uu____9746 = FStar_Syntax_Util.type_u ()  in
                (match uu____9746 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____9718 with
           | (t,uu____9784,g0) ->
               let uu____9798 =
                 FStar_TypeChecker_Util.new_implicit_var
                   "user-provided implicit term" r env1 t
                  in
               (match uu____9798 with
                | (e1,uu____9819,g1) ->
                    let uu____9833 =
                      let uu____9834 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____9834
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____9835 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____9833, uu____9835)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9837 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9847 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____9847)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____9837 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1304_9861 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1304_9861.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1304_9861.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____9864 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____9864 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____9885 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____9885
                       then FStar_Util.Inl t1
                       else
                         (let uu____9894 =
                            let uu____9895 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____9895
                             in
                          FStar_Util.Inr uu____9894)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9897;
             FStar_Syntax_Syntax.vars = uu____9898;_},uu____9899)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9904 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9904
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____9914 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____9914
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____9924;
             FStar_Syntax_Syntax.vars = uu____9925;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____9934 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9934 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____9958 =
                     let uu____9964 =
                       let uu____9966 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____9968 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____9970 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____9966 uu____9968 uu____9970
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____9964)
                      in
                   let uu____9974 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____9958 uu____9974)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____9991 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____9996 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____9996 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____9998 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____9998 with
           | ((us,t),range) ->
               ((let uu____10021 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____10021
                 then
                   let uu____10026 =
                     let uu____10028 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____10028  in
                   let uu____10029 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____10031 = FStar_Range.string_of_range range  in
                   let uu____10033 = FStar_Range.string_of_use_range range
                      in
                   let uu____10035 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____10026 uu____10029 uu____10031 uu____10033
                     uu____10035
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10043 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10043 us  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_constant c ->
          let t = tc_constant env1 top.FStar_Syntax_Syntax.pos c  in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant c)
              FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____10071 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____10071 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____10085 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10085 with
                | (env2,uu____10099) ->
                    let uu____10104 = tc_binders env2 bs1  in
                    (match uu____10104 with
                     | (bs2,env3,g,us) ->
                         let uu____10123 = tc_comp env3 c1  in
                         (match uu____10123 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1384_10142 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1384_10142.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1384_10142.FStar_Syntax_Syntax.vars)
                                }  in
                              (check_smt_pat env3 e1 bs2 c2;
                               (let u = FStar_Syntax_Syntax.U_max (uc :: us)
                                   in
                                let t =
                                  FStar_Syntax_Syntax.mk
                                    (FStar_Syntax_Syntax.Tm_type u)
                                    FStar_Pervasives_Native.None
                                    top.FStar_Syntax_Syntax.pos
                                   in
                                let g1 =
                                  let uu____10153 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10153
                                   in
                                let g2 =
                                  FStar_TypeChecker_Util.close_guard_implicits
                                    env3 bs2 g1
                                   in
                                value_check_expected_typ env0 e1
                                  (FStar_Util.Inl t) g2))))))
      | FStar_Syntax_Syntax.Tm_type u ->
          let u1 = tc_universe env1 u  in
          let t =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u1))
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          let e1 =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u1)
              FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
             in
          value_check_expected_typ env1 e1 (FStar_Util.Inl t)
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_refine (x,phi) ->
          let uu____10169 =
            let uu____10174 =
              let uu____10175 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10175]  in
            FStar_Syntax_Subst.open_term uu____10174 phi  in
          (match uu____10169 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____10203 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10203 with
                | (env2,uu____10217) ->
                    let uu____10222 =
                      let uu____10237 = FStar_List.hd x1  in
                      tc_binder env2 uu____10237  in
                    (match uu____10222 with
                     | (x2,env3,f1,u) ->
                         ((let uu____10273 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____10273
                           then
                             let uu____10276 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____10278 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____10280 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10276 uu____10278 uu____10280
                           else ());
                          (let uu____10287 = FStar_Syntax_Util.type_u ()  in
                           match uu____10287 with
                           | (t_phi,uu____10299) ->
                               let uu____10300 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____10300 with
                                | (phi2,uu____10314,f2) ->
                                    let e1 =
                                      let uu___1422_10319 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1422_10319.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1422_10319.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____10328 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10328
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10356) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____10383 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____10383
            then
              let uu____10386 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1435_10390 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1435_10390.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1435_10390.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10386
            else ());
           (let uu____10406 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____10406 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____10419 ->
          let uu____10420 =
            let uu____10422 = FStar_Syntax_Print.term_to_string top  in
            let uu____10424 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10422
              uu____10424
             in
          failwith uu____10420

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10436 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10438,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10451,FStar_Pervasives_Native.Some msize) ->
            FStar_Syntax_Syntax.tconst
              (match msize with
               | (FStar_Const.Signed ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.int8_lid
               | (FStar_Const.Signed ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.int16_lid
               | (FStar_Const.Signed ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.int32_lid
               | (FStar_Const.Signed ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.int64_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int8 ) ->
                   FStar_Parser_Const.uint8_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int16 ) ->
                   FStar_Parser_Const.uint16_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int32 ) ->
                   FStar_Parser_Const.uint32_lid
               | (FStar_Const.Unsigned ,FStar_Const.Int64 ) ->
                   FStar_Parser_Const.uint64_lid)
        | FStar_Const.Const_string uu____10469 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10475 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10477 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10478 ->
            let uu____10480 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____10480 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10485 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____10486 =
              let uu____10492 =
                let uu____10494 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10494
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10492)  in
            FStar_Errors.raise_error uu____10486 r
        | FStar_Const.Const_set_range_of  ->
            let uu____10498 =
              let uu____10504 =
                let uu____10506 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10506
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10504)  in
            FStar_Errors.raise_error uu____10498 r
        | FStar_Const.Const_reify  ->
            let uu____10510 =
              let uu____10516 =
                let uu____10518 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10518
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10516)  in
            FStar_Errors.raise_error uu____10510 r
        | FStar_Const.Const_reflect uu____10522 ->
            let uu____10523 =
              let uu____10529 =
                let uu____10531 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10531
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10529)  in
            FStar_Errors.raise_error uu____10523 r
        | uu____10535 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedConstant,
                "Unsupported constant") r

and (tc_comp :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.comp * FStar_Syntax_Syntax.universe *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun c  ->
      let c0 = c  in
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uu____10554) ->
          let uu____10563 = FStar_Syntax_Util.type_u ()  in
          (match uu____10563 with
           | (k,u) ->
               let uu____10576 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10576 with
                | (t1,uu____10590,g) ->
                    let uu____10592 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10592, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____10594) ->
          let uu____10603 = FStar_Syntax_Util.type_u ()  in
          (match uu____10603 with
           | (k,u) ->
               let uu____10616 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10616 with
                | (t1,uu____10630,g) ->
                    let uu____10632 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10632, u, g)))
      | FStar_Syntax_Syntax.Comp c1 ->
          let head1 =
            FStar_Syntax_Syntax.fvar c1.FStar_Syntax_Syntax.effect_name
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          let head2 =
            match c1.FStar_Syntax_Syntax.comp_univs with
            | [] -> head1
            | us ->
                FStar_Syntax_Syntax.mk
                  (FStar_Syntax_Syntax.Tm_uinst (head1, us))
                  FStar_Pervasives_Native.None c0.FStar_Syntax_Syntax.pos
             in
          let tc =
            let uu____10642 =
              let uu____10647 =
                let uu____10648 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____10648 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10647  in
            uu____10642 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____10665 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____10665 with
           | (tc1,uu____10679,f) ->
               let uu____10681 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____10681 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____10731 =
                        let uu____10732 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10732.FStar_Syntax_Syntax.n  in
                      match uu____10731 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10735,us) -> us
                      | uu____10741 -> []  in
                    let uu____10742 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____10742 with
                     | (uu____10765,args1) ->
                         let uu____10791 =
                           let uu____10814 = FStar_List.hd args1  in
                           let uu____10831 = FStar_List.tl args1  in
                           (uu____10814, uu____10831)  in
                         (match uu____10791 with
                          | (res,args2) ->
                              let uu____10912 =
                                let uu____10921 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_10949  ->
                                          match uu___5_10949 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____10957 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____10957 with
                                               | (env1,uu____10969) ->
                                                   let uu____10974 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____10974 with
                                                    | (e1,uu____10986,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____10921
                                  FStar_List.unzip
                                 in
                              (match uu____10912 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1564_11027 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1564_11027.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1564_11027.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____11033 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____11033))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____11043 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____11047 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____11057 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____11057
        | FStar_Syntax_Syntax.U_max us ->
            let uu____11061 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____11061
        | FStar_Syntax_Syntax.U_name x ->
            let uu____11065 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____11065
            then u2
            else
              (let uu____11070 =
                 let uu____11072 =
                   let uu____11074 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____11074 " not found"  in
                 Prims.op_Hat "Universe variable " uu____11072  in
               failwith uu____11070)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____11081 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____11081 FStar_Pervasives_Native.snd
         | uu____11090 -> aux u)

and (tc_abs :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.binders ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
            FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      fun bs  ->
        fun body  ->
          let fail1 msg t =
            let uu____11121 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____11121 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____11210 bs2 bs_expected1 =
              match uu____11210 with
              | (env2,subst1) ->
                  (match (bs2, bs_expected1) with
                   | ([],[]) ->
                       (env2, [], FStar_Pervasives_Native.None,
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ((hd1,imp)::bs3,(hd_expected,imp')::bs_expected2) ->
                       ((let special q1 q2 =
                           match (q1, q2) with
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta
                              uu____11401),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11402)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11417),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11418)) -> true
                           | uu____11427 -> false  in
                         let uu____11437 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11440 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____11440 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____11437
                         then
                           let uu____11442 =
                             let uu____11448 =
                               let uu____11450 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11450
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11448)
                              in
                           let uu____11454 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____11442 uu____11454
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____11458 =
                           let uu____11465 =
                             let uu____11466 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____11466.FStar_Syntax_Syntax.n  in
                           match uu____11465 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11477 ->
                               ((let uu____11479 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____11479
                                 then
                                   let uu____11482 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11482
                                 else ());
                                (let uu____11487 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____11487 with
                                 | (t,uu____11501,g1_env) ->
                                     let g2_env =
                                       let uu____11504 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____11504
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11509 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____11509 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11512 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____11518 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____11512 uu____11518
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              FStar_TypeChecker_Util.label_guard
                                                (hd1.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____11521 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____11521)))
                            in
                         match uu____11458 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1662_11547 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1662_11547.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1662_11547.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____11570 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____11570
                                in
                             let uu____11573 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____11573 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____11638 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____11638,
                                    subst3))))
                   | (rest,[]) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inl rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1)
                   | ([],rest) ->
                       (env2, [],
                         (FStar_Pervasives_Native.Some (FStar_Util.Inr rest)),
                         FStar_TypeChecker_Env.trivial_guard, subst1))
               in
            aux (env1, []) bs1 bs_expected  in
          let rec expected_function_typ1 env1 t0 body1 =
            match t0 with
            | FStar_Pervasives_Native.None  ->
                ((match env1.FStar_TypeChecker_Env.letrecs with
                  | [] -> ()
                  | uu____11810 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11820 = tc_binders env1 bs  in
                  match uu____11820 with
                  | (bs1,envbody,g_env,uu____11850) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____11906 =
                    let uu____11907 = FStar_Syntax_Subst.compress t2  in
                    uu____11907.FStar_Syntax_Syntax.n  in
                  match uu____11906 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____11940 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____11960 -> failwith "Impossible");
                       (let uu____11970 = tc_binders env1 bs  in
                        match uu____11970 with
                        | (bs1,envbody,g_env,uu____12012) ->
                            let uu____12013 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12013 with
                             | (envbody1,uu____12051) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____12072;
                         FStar_Syntax_Syntax.pos = uu____12073;
                         FStar_Syntax_Syntax.vars = uu____12074;_},uu____12075)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____12119 -> failwith "Impossible");
                       (let uu____12129 = tc_binders env1 bs  in
                        match uu____12129 with
                        | (bs1,envbody,g_env,uu____12171) ->
                            let uu____12172 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12172 with
                             | (envbody1,uu____12210) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____12232) ->
                      let uu____12237 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____12237 with
                       | (uu____12298,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____12375 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____12375 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12520 c_expected2
                               body3 =
                               match uu____12520 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____12634 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____12634,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12651 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12651
                                           in
                                        let uu____12652 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____12652,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____12669 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____12669
                                        then
                                          let t3 =
                                            FStar_TypeChecker_Normalize.unfold_whnf
                                              env_bs
                                              (FStar_Syntax_Util.comp_result
                                                 c)
                                             in
                                          (match t3.FStar_Syntax_Syntax.n
                                           with
                                           | FStar_Syntax_Syntax.Tm_arrow
                                               (bs_expected3,c_expected3) ->
                                               let uu____12735 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____12735 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____12762 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____12762 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____12817 =
                                                           let uu____12844 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12844,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____12817
                                                           c_expected4 body3))
                                           | uu____12867 ->
                                               let body4 =
                                                 FStar_Syntax_Util.abs
                                                   more_bs body3
                                                   FStar_Pervasives_Native.None
                                                  in
                                               (env_bs, bs2, guard_env, c,
                                                 body4))
                                        else
                                          (let body4 =
                                             FStar_Syntax_Util.abs more_bs
                                               body3
                                               FStar_Pervasives_Native.None
                                              in
                                           (env_bs, bs2, guard_env, c, body4)))
                                in
                             let uu____12896 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____12896 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1788_12961 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1788_12961.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1788_12961.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1788_12961.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1788_12961.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1788_12961.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1788_12961.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1788_12961.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1788_12961.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1788_12961.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1788_12961.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1788_12961.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1788_12961.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1788_12961.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1788_12961.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1788_12961.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1788_12961.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1788_12961.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1788_12961.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1788_12961.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1788_12961.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1788_12961.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1788_12961.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1788_12961.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1788_12961.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1788_12961.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1788_12961.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1788_12961.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1788_12961.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1788_12961.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1788_12961.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1788_12961.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1788_12961.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1788_12961.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1788_12961.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1788_12961.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1788_12961.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1788_12961.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1788_12961.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1788_12961.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1788_12961.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1788_12961.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1788_12961.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___1788_12961.FStar_TypeChecker_Env.strict_args_tab)
                               }  in
                             let uu____12968 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____13034  ->
                                       fun uu____13035  ->
                                         match (uu____13034, uu____13035)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____13126 =
                                               let uu____13133 =
                                                 let uu____13134 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____13134
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____13133 t3  in
                                             (match uu____13126 with
                                              | (t4,uu____13158,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____13171 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1806_13174
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1806_13174.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1806_13174.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____13171 ::
                                                          letrec_binders
                                                    | uu____13175 ->
                                                        letrec_binders
                                                     in
                                                  let uu____13180 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____13180)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____12968 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____13200 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____13200)
                              in
                           let uu____13203 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____13203 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____13279 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____13279 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____13326 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13326))))
                  | uu____13343 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13375 =
                          let uu____13376 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____13376
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____13375
                      else
                        (let uu____13380 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____13380 with
                         | (uu____13429,bs1,uu____13431,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____13463 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____13463 with
          | (env1,topt) ->
              ((let uu____13483 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____13483
                then
                  let uu____13486 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13486
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13500 = expected_function_typ1 env1 topt body  in
                match uu____13500 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____13541 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____13541
                      then
                        let uu____13544 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____13549 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____13554 =
                          let uu____13556 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____13556 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13544 uu____13549 uu____13554
                      else ());
                     (let uu____13566 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____13566
                      then
                        let uu____13571 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____13574 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13571 uu____13574
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____13580 =
                        let should_check_expected_effect =
                          let uu____13593 =
                            let uu____13600 =
                              let uu____13601 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____13601.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____13600)  in
                          match uu____13593 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13607,(FStar_Util.Inr
                                           expected_c,uu____13609),uu____13610))
                              -> false
                          | uu____13660 -> true  in
                        let uu____13668 =
                          tc_term
                            (let uu___1879_13677 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1879_13677.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1879_13677.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1879_13677.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1879_13677.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1879_13677.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1879_13677.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1879_13677.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1879_13677.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1879_13677.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1879_13677.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1879_13677.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1879_13677.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1879_13677.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1879_13677.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1879_13677.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1879_13677.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1879_13677.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1879_13677.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1879_13677.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1879_13677.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1879_13677.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1879_13677.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1879_13677.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1879_13677.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1879_13677.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1879_13677.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1879_13677.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1879_13677.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1879_13677.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1879_13677.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1879_13677.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1879_13677.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1879_13677.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1879_13677.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1879_13677.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1879_13677.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1879_13677.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1879_13677.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1879_13677.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1879_13677.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1879_13677.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1879_13677.FStar_TypeChecker_Env.strict_args_tab)
                             }) body1
                           in
                        match uu____13668 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____13704 =
                                FStar_TypeChecker_Common.lcomp_comp cbody  in
                              (match uu____13704 with
                               | (cbody1,g_lc) ->
                                   let uu____13721 =
                                     check_expected_effect
                                       (let uu___1890_13730 = envbody1  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___1890_13730.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___1890_13730.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___1890_13730.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___1890_13730.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___1890_13730.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___1890_13730.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___1890_13730.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___1890_13730.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___1890_13730.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.is_pattern =
                                            (uu___1890_13730.FStar_TypeChecker_Env.is_pattern);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___1890_13730.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___1890_13730.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___1890_13730.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___1890_13730.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___1890_13730.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            use_eq;
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___1890_13730.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___1890_13730.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___1890_13730.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___1890_13730.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___1890_13730.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___1890_13730.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___1890_13730.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___1890_13730.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___1890_13730.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___1890_13730.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___1890_13730.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___1890_13730.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___1890_13730.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___1890_13730.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___1890_13730.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___1890_13730.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___1890_13730.FStar_TypeChecker_Env.strict_args_tab)
                                        }) c_opt (body2, cbody1)
                                      in
                                   (match uu____13721 with
                                    | (body3,cbody2,guard) ->
                                        let uu____13744 =
                                          let uu____13745 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_lc guard
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 uu____13745
                                           in
                                        (body3, cbody2, uu____13744)))
                            else
                              (let uu____13752 =
                                 FStar_TypeChecker_Common.lcomp_comp cbody
                                  in
                               match uu____13752 with
                               | (cbody1,g_lc) ->
                                   let uu____13769 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 g_lc
                                      in
                                   (body2, cbody1, uu____13769))
                         in
                      match uu____13580 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____13792 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13795 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____13795)
                               in
                            if uu____13792
                            then
                              let uu____13798 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____13799 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____13798
                                uu____13799
                            else
                              (let guard =
                                 let uu____13803 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13803
                                  in
                               guard)
                             in
                          let guard1 =
                            FStar_TypeChecker_Util.close_guard_implicits env1
                              bs1 guard
                             in
                          let tfun_computed =
                            FStar_Syntax_Util.arrow bs1 cbody  in
                          let e =
                            FStar_Syntax_Util.abs bs1 body2
                              (FStar_Pervasives_Native.Some
                                 (FStar_Syntax_Util.residual_comp_of_comp
                                    (FStar_Util.dflt cbody c_opt)))
                             in
                          let uu____13817 =
                            match tfun_opt with
                            | FStar_Pervasives_Native.Some t ->
                                let t1 = FStar_Syntax_Subst.compress t  in
                                let t_annot =
                                  match topt with
                                  | FStar_Pervasives_Native.Some t2 -> t2
                                  | FStar_Pervasives_Native.None  ->
                                      failwith
                                        "Impossible! tc_abs: if tfun_computed is Some, expected topt to also be Some"
                                   in
                                (match t1.FStar_Syntax_Syntax.n with
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13841
                                     -> (e, t_annot, guard1)
                                 | uu____13856 ->
                                     let uu____13857 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____13857 with
                                      | (e1,guard') ->
                                          let uu____13870 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____13870)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____13817 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____13881 =
                                 let uu____13886 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13886 guard2
                                  in
                               (match uu____13881 with
                                | (c1,g) -> (e1, c1, g)))))))

and (check_application_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun ghead  ->
          fun args  ->
            fun expected_topt  ->
              let n_args = FStar_List.length args  in
              let r = FStar_TypeChecker_Env.get_range env  in
              let thead = FStar_Syntax_Util.comp_result chead  in
              (let uu____13937 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____13937
               then
                 let uu____13940 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____13942 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____13940
                   uu____13942
               else ());
              (let monadic_application uu____14024 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14024 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____14093 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____14093 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____14107 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14123 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14123
                                   in
                                (cres1, g)
                            | uu____14124 ->
                                let g =
                                  let uu____14134 =
                                    let uu____14135 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____14135
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14134
                                   in
                                let uu____14136 =
                                  let uu____14137 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____14137
                                   in
                                (uu____14136, g)
                             in
                          (match uu____14107 with
                           | (cres2,guard1) ->
                               ((let uu____14147 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____14147
                                 then
                                   let uu____14150 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14150
                                 else ());
                                (let uu____14155 =
                                   let uu____14160 =
                                     let uu____14161 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____14161
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____14162 =
                                     let uu____14163 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____14163
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____14160, uu____14162)  in
                                 match uu____14155 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____14187  ->
                                                 match uu____14187 with
                                                 | (uu____14197,uu____14198,lc)
                                                     ->
                                                     (let uu____14206 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____14206)
                                                       ||
                                                       (FStar_TypeChecker_Util.should_not_inline_lc
                                                          lc)) arg_comps_rev)
                                          in
                                       let term =
                                         FStar_Syntax_Syntax.mk_Tm_app head2
                                           (FStar_List.rev arg_rets_rev)
                                           FStar_Pervasives_Native.None
                                           head2.FStar_Syntax_Syntax.pos
                                          in
                                       let uu____14219 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____14219
                                       then
                                         ((let uu____14223 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____14223
                                           then
                                             let uu____14226 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____14226
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____14234 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____14234
                                           then
                                             let uu____14237 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____14237
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____14268  ->
                                              match uu____14268 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____14310 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14310
                                                    then
                                                      let uu____14313 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____14318 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____14320 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____14313
                                                        uu____14318
                                                        uu____14320
                                                    else ());
                                                   (let uu____14325 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____14325
                                                    then
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        (FStar_Pervasives_Native.Some
                                                           e) c (x, out_c)
                                                    else
                                                      FStar_TypeChecker_Util.bind
                                                        e.FStar_Syntax_Syntax.pos
                                                        env
                                                        FStar_Pervasives_Native.None
                                                        c (x, out_c)))) cres4
                                         arg_comps_rev
                                        in
                                     let comp1 =
                                       (let uu____14336 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____14336
                                        then
                                          let uu____14339 =
                                            FStar_Syntax_Print.term_to_string
                                              head2
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____14339
                                        else ());
                                       (let uu____14344 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____14344
                                        then
                                          FStar_TypeChecker_Util.bind
                                            head2.FStar_Syntax_Syntax.pos env
                                            (FStar_Pervasives_Native.Some
                                               head2) chead2
                                            (FStar_Pervasives_Native.None,
                                              comp)
                                        else
                                          FStar_TypeChecker_Util.bind
                                            head2.FStar_Syntax_Syntax.pos env
                                            FStar_Pervasives_Native.None
                                            chead2
                                            (FStar_Pervasives_Native.None,
                                              comp))
                                        in
                                     let shortcuts_evaluation_order =
                                       let uu____14355 =
                                         let uu____14356 =
                                           FStar_Syntax_Subst.compress head2
                                            in
                                         uu____14356.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14355 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____14361 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____14384  ->
                                                  match uu____14384 with
                                                  | (arg,uu____14398,uu____14399)
                                                      -> arg :: args1) []
                                             arg_comps_rev
                                            in
                                         let app =
                                           FStar_Syntax_Syntax.mk_Tm_app
                                             head2 args1
                                             FStar_Pervasives_Native.None r
                                            in
                                         let app1 =
                                           FStar_TypeChecker_Util.maybe_lift
                                             env app
                                             cres4.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.eff_name
                                             comp1.FStar_TypeChecker_Common.res_typ
                                            in
                                         FStar_TypeChecker_Util.maybe_monadic
                                           env app1
                                           comp1.FStar_TypeChecker_Common.eff_name
                                           comp1.FStar_TypeChecker_Common.res_typ
                                       else
                                         (let uu____14410 =
                                            let map_fun uu____14476 =
                                              match uu____14476 with
                                              | ((e,q),uu____14517,c) ->
                                                  ((let uu____14540 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14540
                                                    then
                                                      let uu____14543 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____14545 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____14543
                                                        uu____14545
                                                    else ());
                                                   (let uu____14550 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____14550
                                                    then
                                                      ((let uu____14576 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____14576
                                                        then
                                                          FStar_Util.print_string
                                                            "... not lifting\n"
                                                        else ());
                                                       (FStar_Pervasives_Native.None,
                                                         (e, q)))
                                                    else
                                                      (let warn_effectful_args
                                                         =
                                                         (FStar_TypeChecker_Util.must_erase_for_extraction
                                                            env
                                                            chead2.FStar_TypeChecker_Common.res_typ)
                                                           &&
                                                           (let uu____14617 =
                                                              let uu____14619
                                                                =
                                                                let uu____14620
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head2
                                                                   in
                                                                uu____14620.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____14619
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____14625
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____14625
                                                              | uu____14627
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____14617)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____14631 =
                                                            let uu____14637 =
                                                              let uu____14639
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____14641
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head2
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____14639
                                                                (c.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                                                                uu____14641
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____14637)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____14631)
                                                       else ();
                                                       (let uu____14648 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____14648
                                                        then
                                                          FStar_Util.print_string
                                                            "... lifting!\n"
                                                        else ());
                                                       (let x =
                                                          FStar_Syntax_Syntax.new_bv
                                                            FStar_Pervasives_Native.None
                                                            c.FStar_TypeChecker_Common.res_typ
                                                           in
                                                        let e1 =
                                                          FStar_TypeChecker_Util.maybe_lift
                                                            env e
                                                            c.FStar_TypeChecker_Common.eff_name
                                                            comp1.FStar_TypeChecker_Common.eff_name
                                                            c.FStar_TypeChecker_Common.res_typ
                                                           in
                                                        let uu____14656 =
                                                          let uu____14665 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____14665, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____14656)))))
                                               in
                                            let uu____14694 =
                                              let uu____14725 =
                                                let uu____14754 =
                                                  let uu____14765 =
                                                    let uu____14774 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head2
                                                       in
                                                    (uu____14774,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____14765 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____14754
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____14725
                                               in
                                            match uu____14694 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____14975 =
                                                  let uu____14976 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____14976
                                                   in
                                                let uu____14997 =
                                                  let uu____14998 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____14998
                                                   in
                                                (lifted_args, uu____14975,
                                                  uu____14997)
                                             in
                                          match uu____14410 with
                                          | (lifted_args,head3,args1) ->
                                              let app =
                                                FStar_Syntax_Syntax.mk_Tm_app
                                                  head3 args1
                                                  FStar_Pervasives_Native.None
                                                  r
                                                 in
                                              let app1 =
                                                FStar_TypeChecker_Util.maybe_lift
                                                  env app
                                                  cres4.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ
                                                 in
                                              let app2 =
                                                FStar_TypeChecker_Util.maybe_monadic
                                                  env app1
                                                  comp1.FStar_TypeChecker_Common.eff_name
                                                  comp1.FStar_TypeChecker_Common.res_typ
                                                 in
                                              let bind_lifted_args e
                                                uu___6_15109 =
                                                match uu___6_15109 with
                                                | FStar_Pervasives_Native.None
                                                     -> e
                                                | FStar_Pervasives_Native.Some
                                                    (x,m,t,e1) ->
                                                    let lb =
                                                      FStar_Syntax_Util.mk_letbinding
                                                        (FStar_Util.Inl x) []
                                                        t m e1 []
                                                        e1.FStar_Syntax_Syntax.pos
                                                       in
                                                    let letbinding =
                                                      let uu____15170 =
                                                        let uu____15177 =
                                                          let uu____15178 =
                                                            let uu____15192 =
                                                              let uu____15195
                                                                =
                                                                let uu____15196
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____15196]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____15195 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____15192)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____15178
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____15177
                                                         in
                                                      uu____15170
                                                        FStar_Pervasives_Native.None
                                                        e.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (letbinding,
                                                           (FStar_Syntax_Syntax.Meta_monadic
                                                              (m,
                                                                (comp1.FStar_TypeChecker_Common.res_typ)))))
                                                      FStar_Pervasives_Native.None
                                                      e.FStar_Syntax_Syntax.pos
                                                 in
                                              FStar_List.fold_left
                                                bind_lifted_args app2
                                                lifted_args)
                                        in
                                     let uu____15248 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____15248 with
                                      | (comp2,g) ->
                                          ((let uu____15266 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____15266
                                            then
                                              let uu____15269 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____15271 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____15269 uu____15271
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____15352 bs args1 =
                 match uu____15352 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15491))::rest,
                         (uu____15493,FStar_Pervasives_Native.None )::uu____15494)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____15555 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____15555 with
                           | (t1,g_ex) ->
                               let uu____15568 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____15568 with
                                | (varg,uu____15589,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____15617 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____15617)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____15626 =
                                      let uu____15661 =
                                        let uu____15672 =
                                          let uu____15681 =
                                            let uu____15682 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____15682
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15681)
                                           in
                                        uu____15672 :: outargs  in
                                      (subst2, uu____15661, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____15626 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____15728,FStar_Pervasives_Native.None
                                                                 )::uu____15729)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____15791 = tc_tactic env tau1  in
                          (match uu____15791 with
                           | (tau2,uu____15805,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15808 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____15808 with
                                | (t1,g_ex) ->
                                    let uu____15821 =
                                      let uu____15834 =
                                        let uu____15841 =
                                          let uu____15846 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____15846, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____15841
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15834
                                       in
                                    (match uu____15821 with
                                     | (varg,uu____15859,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____15887 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____15887)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____15896 =
                                           let uu____15931 =
                                             let uu____15942 =
                                               let uu____15951 =
                                                 let uu____15952 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____15952
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____15951)
                                                in
                                             uu____15942 :: outargs  in
                                           (subst2, uu____15931, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____15896 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16068,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16069)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____16080),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16081)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____16089),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16090)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____16105 ->
                                let uu____16114 =
                                  let uu____16120 =
                                    let uu____16122 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____16124 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____16126 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____16128 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16122 uu____16124 uu____16126
                                      uu____16128
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16120)
                                   in
                                FStar_Errors.raise_error uu____16114
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2167_16135 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2167_16135.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2167_16135.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____16137 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____16137
                             then
                               let uu____16140 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____16142 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16144 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16146 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____16148 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16140 uu____16142 uu____16144
                                 uu____16146 uu____16148
                             else ());
                            (let uu____16153 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____16153 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2176_16168 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2176_16168.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2176_16168.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2176_16168.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2176_16168.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2176_16168.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2176_16168.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2176_16168.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2176_16168.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2176_16168.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2176_16168.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2176_16168.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2176_16168.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2176_16168.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2176_16168.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2176_16168.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2176_16168.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2176_16168.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2176_16168.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2176_16168.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2176_16168.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2176_16168.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2176_16168.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2176_16168.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2176_16168.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2176_16168.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2176_16168.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2176_16168.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2176_16168.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2176_16168.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2176_16168.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2176_16168.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2176_16168.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2176_16168.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2176_16168.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2176_16168.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2176_16168.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2176_16168.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2176_16168.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2176_16168.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2176_16168.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2176_16168.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2176_16168.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2176_16168.FStar_TypeChecker_Env.strict_args_tab)
                                   }  in
                                 ((let uu____16170 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____16170
                                   then
                                     let uu____16173 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____16175 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____16177 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____16173 uu____16175 uu____16177
                                   else ());
                                  (let uu____16182 = tc_term env2 e  in
                                   match uu____16182 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____16199 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____16199
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____16222 =
                                           let uu____16225 =
                                             let uu____16234 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16234
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____16225
                                            in
                                         (uu____16222, aq)  in
                                       let uu____16243 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____16243
                                       then
                                         let subst2 =
                                           let uu____16253 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____16253 e1
                                            in
                                         tc_args head_info
                                           (subst2,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, fvs)
                                           rest rest'
                                       else
                                         tc_args head_info
                                           (subst1,
                                             ((arg,
                                                (FStar_Pervasives_Native.Some
                                                   x1), c) :: outargs),
                                             (xterm :: arg_rets), g1, (x1 ::
                                             fvs)) rest rest')))))
                      | (uu____16352,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____16388) ->
                          let uu____16439 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____16439 with
                           | (head2,chead1,ghead1) ->
                               let uu____16461 =
                                 let uu____16466 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____16466
                                   (fun uu____16483  ->
                                      match uu____16483 with
                                      | (c,g1) ->
                                          let uu____16494 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____16494))
                                  in
                               (match uu____16461 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____16537 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____16537
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____16568 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____16568 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head2, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____16591 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____16591
                                                 then
                                                   FStar_Errors.log_issue
                                                     tres1.FStar_Syntax_Syntax.pos
                                                     (FStar_Errors.Warning_RedundantExplicitCurrying,
                                                       "Potentially redundant explicit currying of a function type")
                                                 else ());
                                                tc_args head_info1
                                                  ([], [], [],
                                                    FStar_TypeChecker_Env.trivial_guard,
                                                    []) bs2 args1))
                                      | uu____16638 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              FStar_TypeChecker_Normalize.unfold_whnf
                                                env tres2
                                               in
                                            let uu____16646 =
                                              let uu____16647 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____16647.FStar_Syntax_Syntax.n
                                               in
                                            match uu____16646 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____16650;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____16651;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____16653)
                                                -> norm_tres tres4
                                            | uu____16661 -> tres3  in
                                          let uu____16662 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____16662
                                      | uu____16664 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____16667 ->
                                          let uu____16668 =
                                            let uu____16674 =
                                              let uu____16676 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____16678 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____16680 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____16676 uu____16678
                                                uu____16680
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____16674)
                                             in
                                          let uu____16684 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____16668 uu____16684
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____16714 =
                   let uu____16715 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____16715.FStar_Syntax_Syntax.n  in
                 match uu____16714 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16724 ->
                     let uu____16737 =
                       FStar_List.fold_right
                         (fun uu____16768  ->
                            fun uu____16769  ->
                              match uu____16769 with
                              | (bs,guard1) ->
                                  let uu____16796 =
                                    let uu____16809 =
                                      let uu____16810 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16810
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16809
                                     in
                                  (match uu____16796 with
                                   | (t,uu____16827,g) ->
                                       let uu____16841 =
                                         let uu____16844 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16844 :: bs  in
                                       let uu____16845 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16841, uu____16845))) args
                         ([], guard)
                        in
                     (match uu____16737 with
                      | (bs,guard1) ->
                          let uu____16862 =
                            let uu____16869 =
                              let uu____16882 =
                                let uu____16883 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16883
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16882
                               in
                            match uu____16869 with
                            | (t,uu____16900,g) ->
                                let uu____16914 = FStar_Options.ml_ish ()  in
                                if uu____16914
                                then
                                  let uu____16923 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____16926 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____16923, uu____16926)
                                else
                                  (let uu____16931 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____16934 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____16931, uu____16934))
                             in
                          (match uu____16862 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____16953 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____16953
                                 then
                                   let uu____16957 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____16959 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____16961 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____16957 uu____16959 uu____16961
                                 else ());
                                (let g =
                                   let uu____16967 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____16967
                                    in
                                 let uu____16968 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____16968))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____16969;
                        FStar_Syntax_Syntax.pos = uu____16970;
                        FStar_Syntax_Syntax.vars = uu____16971;_},uu____16972)
                     ->
                     let uu____17009 =
                       FStar_List.fold_right
                         (fun uu____17040  ->
                            fun uu____17041  ->
                              match uu____17041 with
                              | (bs,guard1) ->
                                  let uu____17068 =
                                    let uu____17081 =
                                      let uu____17082 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17082
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17081
                                     in
                                  (match uu____17068 with
                                   | (t,uu____17099,g) ->
                                       let uu____17113 =
                                         let uu____17116 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17116 :: bs  in
                                       let uu____17117 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17113, uu____17117))) args
                         ([], guard)
                        in
                     (match uu____17009 with
                      | (bs,guard1) ->
                          let uu____17134 =
                            let uu____17141 =
                              let uu____17154 =
                                let uu____17155 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17155
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17154
                               in
                            match uu____17141 with
                            | (t,uu____17172,g) ->
                                let uu____17186 = FStar_Options.ml_ish ()  in
                                if uu____17186
                                then
                                  let uu____17195 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17198 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17195, uu____17198)
                                else
                                  (let uu____17203 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17206 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17203, uu____17206))
                             in
                          (match uu____17134 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17225 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17225
                                 then
                                   let uu____17229 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____17231 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17233 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17229 uu____17231 uu____17233
                                 else ());
                                (let g =
                                   let uu____17239 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17239
                                    in
                                 let uu____17240 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17240))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____17263 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____17263 with
                      | (bs1,c1) ->
                          let head_info = (head1, chead, ghead, c1)  in
                          ((let uu____17286 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____17286
                            then
                              let uu____17289 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17291 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____17293 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____17296 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17289 uu____17291 uu____17293
                                uu____17296
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____17342) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____17348,uu____17349) ->
                     check_function_app t guard
                 | uu____17390 ->
                     let uu____17391 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____17391
                       head1.FStar_Syntax_Syntax.pos
                  in
               check_function_app thead FStar_TypeChecker_Env.trivial_guard)

and (check_short_circuit_args :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp ->
        FStar_TypeChecker_Env.guard_t ->
          (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
            FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
            Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
                FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun head1  ->
      fun chead  ->
        fun g_head  ->
          fun args  ->
            fun expected_topt  ->
              let r = FStar_TypeChecker_Env.get_range env  in
              let tf =
                FStar_Syntax_Subst.compress
                  (FStar_Syntax_Util.comp_result chead)
                 in
              match tf.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_arrow (bs,c) when
                  (FStar_Syntax_Util.is_total_comp c) &&
                    ((FStar_List.length bs) = (FStar_List.length args))
                  ->
                  let res_t = FStar_Syntax_Util.comp_result c  in
                  let uu____17474 =
                    FStar_List.fold_left2
                      (fun uu____17543  ->
                         fun uu____17544  ->
                           fun uu____17545  ->
                             match (uu____17543, uu____17544, uu____17545)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____17698 =
                                     let uu____17700 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____17700 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____17698
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17706 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____17706 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____17735 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17735 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17740 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____17740)
                                              &&
                                              (let uu____17743 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____17743))
                                          in
                                       let uu____17745 =
                                         let uu____17756 =
                                           let uu____17767 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____17767]  in
                                         FStar_List.append seen uu____17756
                                          in
                                       let uu____17800 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____17745, uu____17800, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____17474 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____17868 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____17868
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____17871 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____17871 with | (c2,g) -> (e, c2, g)))
              | uu____17888 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.term *
          FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun pat_t  ->
      fun p0  ->
        let fail1 msg =
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_MismatchedPatternType, msg)
            p0.FStar_Syntax_Syntax.p
           in
        let expected_pat_typ env1 pos scrutinee_t =
          let rec aux norm1 t =
            let t1 = FStar_Syntax_Util.unrefine t  in
            let uu____17979 = FStar_Syntax_Util.head_and_args t1  in
            match uu____17979 with
            | (head1,args) ->
                let uu____18022 =
                  let uu____18023 = FStar_Syntax_Subst.compress head1  in
                  uu____18023.FStar_Syntax_Syntax.n  in
                (match uu____18022 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18027;
                        FStar_Syntax_Syntax.vars = uu____18028;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18035 ->
                     if norm1
                     then t1
                     else
                       (let uu____18039 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____18039))
          
          and unfold_once t f us args =
            let uu____18057 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____18057
            then t
            else
              (let uu____18062 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____18062 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18082 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____18082 with
                    | (uu____18087,head_def) ->
                        let t' =
                          FStar_Syntax_Syntax.mk_Tm_app head_def args
                            FStar_Pervasives_Native.None
                            t.FStar_Syntax_Syntax.pos
                           in
                        let t'1 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.Beta;
                            FStar_TypeChecker_Env.Iota] env1 t'
                           in
                        aux false t'1))
           in
          let uu____18094 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____18094  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18113 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____18113
           then
             let uu____18118 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____18120 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18118 uu____18120
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____18140 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____18142 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18140 uu____18142 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____18146 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____18146 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____18190 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____18190 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____18191;
                    FStar_Syntax_Syntax.pos = uu____18192;
                    FStar_Syntax_Syntax.vars = uu____18193;_} ->
                    let uu____18196 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____18196 with
                     | (head_p,args_p) ->
                         let uu____18239 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____18239
                         then
                           let uu____18242 =
                             let uu____18243 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____18243.FStar_Syntax_Syntax.n  in
                           (match uu____18242 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____18248 =
                                    let uu____18250 =
                                      let uu____18252 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18252
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18250
                                     in
                                  if uu____18248
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____18280 =
                                    let uu____18305 =
                                      let uu____18309 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18309
                                       in
                                    match uu____18305 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____18358 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____18358 with
                                         | (params_p,uu____18416) ->
                                             let uu____18457 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____18457 with
                                              | (params_s,uu____18515) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____18280 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____18644  ->
                                             fun uu____18645  ->
                                               match (uu____18644,
                                                       uu____18645)
                                               with
                                               | ((p,uu____18679),(s,uu____18681))
                                                   ->
                                                   let uu____18714 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____18714 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____18717 =
                                                          let uu____18719 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____18721 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18719
                                                            uu____18721
                                                           in
                                                        fail2 uu____18717
                                                    | FStar_Pervasives_Native.Some
                                                        g ->
                                                        let g1 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            env1 g
                                                           in
                                                        FStar_TypeChecker_Env.conj_guard
                                                          g1 out))
                                        FStar_TypeChecker_Env.trivial_guard
                                        params_p params_s))
                            | uu____18726 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18730 =
                              let uu____18732 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____18734 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18732 uu____18734
                               in
                            fail2 uu____18730))
                | uu____18737 ->
                    let uu____18738 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____18738 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____18775 = FStar_Syntax_Util.head_and_args e  in
          match uu____18775 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18839 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18839 with
                    | (us,t_f) ->
                        let uu____18856 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____18856 with
                         | (formals,t) ->
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____18985 formals1 args1 =
                                 match uu____18985 with
                                 | (subst1,args_out,bvs,guard) ->
                                     (match (formals1, args1) with
                                      | ([],[]) ->
                                          let head2 =
                                            FStar_Syntax_Syntax.mk_Tm_uinst
                                              head1 us
                                             in
                                          let pat_e =
                                            FStar_Syntax_Syntax.mk_Tm_app
                                              head2 args_out
                                              FStar_Pervasives_Native.None
                                              e.FStar_Syntax_Syntax.pos
                                             in
                                          let uu____19130 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____19130, bvs, guard)
                                      | ((f1,uu____19136)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____19194 =
                                            let uu____19215 =
                                              let uu____19216 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____19216.FStar_Syntax_Syntax.n
                                               in
                                            match uu____19215 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2482_19241 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2482_19241.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2482_19241.FStar_Syntax_Syntax.index);
                                                    FStar_Syntax_Syntax.sort
                                                      = t_f1
                                                  }  in
                                                let a1 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    x1
                                                   in
                                                let subst2 =
                                                  (FStar_Syntax_Syntax.NT
                                                     (f1, a1))
                                                  :: subst1  in
                                                ((a1, imp_a), subst2,
                                                  (FStar_List.append bvs [x1]),
                                                  FStar_TypeChecker_Env.trivial_guard)
                                            | FStar_Syntax_Syntax.Tm_uvar
                                                uu____19264 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____19278 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____19278 with
                                                 | (a1,uu____19306,g) ->
                                                     let g1 =
                                                       FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                         env2 g
                                                        in
                                                     let subst2 =
                                                       (FStar_Syntax_Syntax.NT
                                                          (f1, a1))
                                                       :: subst1  in
                                                     ((a1, imp_a), subst2,
                                                       bvs, g1))
                                            | uu____19330 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____19194 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____19392 =
                                                 let uu____19415 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19415)
                                                  in
                                               aux uu____19392 formals2 args2)
                                      | uu____19454 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19510 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____19559 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19559
           then
             let uu____19564 = FStar_Syntax_Print.pat_to_string p  in
             let uu____19566 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19564
               uu____19566
           else ());
          (match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19581 ->
               let uu____19588 =
                 let uu____19590 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19590
                  in
               failwith uu____19588
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2514_19605 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2514_19605.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2514_19605.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19606 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19606,
                 (let uu___2517_19610 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2517_19610.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2521_19613 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2521_19613.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2521_19613.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19614 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], uu____19614,
                 (let uu___2524_19618 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2524_19618.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard)
           | FStar_Syntax_Syntax.Pat_constant uu____19619 ->
               let uu____19620 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____19620 with
                | (uu____19642,e_c,uu____19644,uu____19645) ->
                    let uu____19650 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____19650 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____19673 =
                              let uu____19675 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____19675  in
                            if uu____19673
                            then
                              let uu____19678 =
                                let uu____19680 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____19682 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____19680 uu____19682
                                 in
                              fail1 uu____19678
                            else ());
                           ([], e_c1, p, FStar_TypeChecker_Env.trivial_guard)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____19740  ->
                        match uu____19740 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____19770
                                 -> (p1, b)
                             | uu____19780 ->
                                 let uu____19781 =
                                   let uu____19784 =
                                     let uu____19785 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____19785
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____19784
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____19781, b))) sub_pats
                    in
                 let uu___2552_19789 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2552_19789.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____19834  ->
                         match uu____19834 with
                         | (x,uu____19844) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____19852
                                  -> false
                              | uu____19860 -> true)))
                  in
               let uu____19862 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____19862 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____19899 =
                          let uu____19901 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____19903 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____19905 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____19912 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____19901 uu____19903 uu____19905 uu____19912
                           in
                        failwith uu____19899)
                     else ();
                     (let uu____19917 =
                        let uu____19926 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____19926 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard) ->
                            let g' =
                              let uu____19954 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____19954  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____19957 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____19957
                              then
                                let uu____19962 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____19964 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____19966 =
                                  let uu____19968 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____19976 =
                                           let uu____19978 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____19980 =
                                             let uu____19982 =
                                               let uu____19984 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____19984 ")"
                                                in
                                             Prims.op_Hat " : " uu____19982
                                              in
                                           Prims.op_Hat uu____19978
                                             uu____19980
                                            in
                                         Prims.op_Hat "(" uu____19976)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____19968
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____19962 uu____19964 uu____19966
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1))
                         in
                      match uu____19917 with
                      | (simple_pat_e1,simple_bvs1,g1) ->
                          let uu____20016 =
                            let uu____20038 =
                              let uu____20060 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], uu____20060)  in
                            FStar_List.fold_left2
                              (fun uu____20121  ->
                                 fun uu____20122  ->
                                   fun x  ->
                                     match (uu____20121, uu____20122) with
                                     | ((env2,bvs,pats,subst1,g),(p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____20255 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____20255 with
                                          | (bvs_p,e_p,p2,g') ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let uu____20296 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____20296))) uu____20038
                              sub_pats1 simple_bvs1
                             in
                          (match uu____20016 with
                           | (_env,bvs,checked_sub_pats,subst1,g) ->
                               let pat_e =
                                 FStar_Syntax_Subst.subst subst1
                                   simple_pat_e1
                                  in
                               let reconstruct_nested_pat pat =
                                 let rec aux simple_pats bvs1 sub_pats2 =
                                   match simple_pats with
                                   | [] -> []
                                   | (hd1,b)::simple_pats1 ->
                                       (match hd1.FStar_Syntax_Syntax.v with
                                        | FStar_Syntax_Syntax.Pat_dot_term
                                            (x,e) ->
                                            let e1 =
                                              FStar_Syntax_Subst.subst subst1
                                                e
                                               in
                                            let hd2 =
                                              let uu___2624_20508 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2624_20508.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____20513 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____20513
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____20557)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____20594 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____20594
                                             | uu____20614 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____20640 ->
                                            failwith
                                              "Impossible: expected a simple pattern")
                                    in
                                 match pat.FStar_Syntax_Syntax.v with
                                 | FStar_Syntax_Syntax.Pat_cons
                                     (fv1,simple_pats) ->
                                     let nested_pats =
                                       aux simple_pats simple_bvs1
                                         checked_sub_pats
                                        in
                                     let uu___2645_20683 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2645_20683.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____20695 -> failwith "Impossible"  in
                               let uu____20699 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, pat_e, uu____20699, g))))))
           in
        (let uu____20703 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____20703
         then
           let uu____20708 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____20708
         else ());
        (let uu____20713 =
           let uu____20724 =
             let uu___2650_20725 =
               let uu____20726 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____20726 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2650_20725.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2650_20725.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2650_20725.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2650_20725.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2650_20725.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2650_20725.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2650_20725.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2650_20725.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2650_20725.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2650_20725.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2650_20725.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2650_20725.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2650_20725.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2650_20725.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2650_20725.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2650_20725.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2650_20725.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2650_20725.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2650_20725.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2650_20725.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2650_20725.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2650_20725.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2650_20725.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2650_20725.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2650_20725.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2650_20725.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2650_20725.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2650_20725.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2650_20725.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2650_20725.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2650_20725.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2650_20725.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2650_20725.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2650_20725.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2650_20725.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2650_20725.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2650_20725.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2650_20725.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2650_20725.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2650_20725.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2650_20725.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2650_20725.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2650_20725.FStar_TypeChecker_Env.strict_args_tab)
             }  in
           let uu____20742 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____20724 uu____20742 pat_t  in
         match uu____20713 with
         | (bvs,pat_e,pat,g) ->
             ((let uu____20766 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____20766
               then
                 let uu____20771 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____20773 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____20771
                   uu____20773
               else ());
              (let uu____20778 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____20779 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, uu____20778, pat_e, uu____20779, g))))

and (tc_eqn :
  FStar_Syntax_Syntax.bv ->
    FStar_TypeChecker_Env.env ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) ->
        ((FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
          FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) *
          FStar_Syntax_Syntax.term * FStar_Ident.lident *
          FStar_Syntax_Syntax.cflag Prims.list *
          (Prims.bool -> FStar_TypeChecker_Common.lcomp) *
          FStar_TypeChecker_Common.guard_t))
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____20825 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____20825 with
        | (pattern,when_clause,branch_exp) ->
            let uu____20871 = branch1  in
            (match uu____20871 with
             | (cpat,uu____20913,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____20935 =
                   let uu____20942 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____20942
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____20935 with
                  | (scrutinee_env,uu____20976) ->
                      let uu____20981 = tc_pat env pat_t pattern  in
                      (match uu____20981 with
                       | (pattern1,pat_bvs1,pat_env,pat_exp,norm_pat_exp,guard_pat)
                           ->
                           let uu____21032 =
                             match when_clause with
                             | FStar_Pervasives_Native.None  ->
                                 (FStar_Pervasives_Native.None,
                                   FStar_TypeChecker_Env.trivial_guard)
                             | FStar_Pervasives_Native.Some e ->
                                 let uu____21062 =
                                   FStar_TypeChecker_Env.should_verify env
                                    in
                                 if uu____21062
                                 then
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_WhenClauseNotSupported,
                                       "When clauses are not yet supported in --verify mode; they will be some day")
                                     e.FStar_Syntax_Syntax.pos
                                 else
                                   (let uu____21085 =
                                      let uu____21092 =
                                        FStar_TypeChecker_Env.set_expected_typ
                                          pat_env FStar_Syntax_Util.t_bool
                                         in
                                      tc_term uu____21092 e  in
                                    match uu____21085 with
                                    | (e1,c,g) ->
                                        ((FStar_Pervasives_Native.Some e1),
                                          g))
                              in
                           (match uu____21032 with
                            | (when_clause1,g_when) ->
                                let uu____21146 = tc_term pat_env branch_exp
                                   in
                                (match uu____21146 with
                                 | (branch_exp1,c,g_branch) ->
                                     (FStar_TypeChecker_Env.def_check_guard_wf
                                        cbr.FStar_Syntax_Syntax.pos
                                        "tc_eqn.1" pat_env g_branch;
                                      (let when_condition =
                                         match when_clause1 with
                                         | FStar_Pervasives_Native.None  ->
                                             FStar_Pervasives_Native.None
                                         | FStar_Pervasives_Native.Some w ->
                                             let uu____21202 =
                                               FStar_Syntax_Util.mk_eq2
                                                 FStar_Syntax_Syntax.U_zero
                                                 FStar_Syntax_Util.t_bool w
                                                 FStar_Syntax_Util.exp_true_bool
                                                in
                                             FStar_All.pipe_left
                                               (fun _21213  ->
                                                  FStar_Pervasives_Native.Some
                                                    _21213) uu____21202
                                          in
                                       let uu____21214 =
                                         let eqs =
                                           let uu____21236 =
                                             let uu____21238 =
                                               FStar_TypeChecker_Env.should_verify
                                                 env
                                                in
                                             Prims.op_Negation uu____21238
                                              in
                                           if uu____21236
                                           then FStar_Pervasives_Native.None
                                           else
                                             (let e =
                                                FStar_Syntax_Subst.compress
                                                  pat_exp
                                                 in
                                              match e.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_uvar
                                                  uu____21254 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_constant
                                                  uu____21269 ->
                                                  FStar_Pervasives_Native.None
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  uu____21272 ->
                                                  FStar_Pervasives_Native.None
                                              | uu____21275 ->
                                                  let uu____21276 =
                                                    let uu____21279 =
                                                      env.FStar_TypeChecker_Env.universe_of
                                                        env pat_t
                                                       in
                                                    FStar_Syntax_Util.mk_eq2
                                                      uu____21279 pat_t
                                                      scrutinee_tm e
                                                     in
                                                  FStar_Pervasives_Native.Some
                                                    uu____21276)
                                            in
                                         let uu____21282 =
                                           FStar_TypeChecker_Util.strengthen_precondition
                                             FStar_Pervasives_Native.None env
                                             branch_exp1 c g_branch
                                            in
                                         match uu____21282 with
                                         | (c1,g_branch1) ->
                                             let uu____21309 =
                                               match (eqs, when_condition)
                                               with
                                               | uu____21326 when
                                                   let uu____21339 =
                                                     FStar_TypeChecker_Env.should_verify
                                                       env
                                                      in
                                                   Prims.op_Negation
                                                     uu____21339
                                                   -> (c1, g_when)
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.None
                                                  ) -> (c1, g_when)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.None
                                                  ) ->
                                                   let gf =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       gf
                                                      in
                                                   let uu____21370 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 gf
                                                      in
                                                   let uu____21371 =
                                                     FStar_TypeChecker_Env.imp_guard
                                                       g g_when
                                                      in
                                                   (uu____21370, uu____21371)
                                               | (FStar_Pervasives_Native.Some
                                                  f,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_f =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       f
                                                      in
                                                   let g_fw =
                                                     let uu____21392 =
                                                       FStar_Syntax_Util.mk_conj
                                                         f w
                                                        in
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       uu____21392
                                                      in
                                                   let uu____21393 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_fw
                                                      in
                                                   let uu____21394 =
                                                     let uu____21395 =
                                                       FStar_TypeChecker_Env.guard_of_guard_formula
                                                         g_f
                                                        in
                                                     FStar_TypeChecker_Env.imp_guard
                                                       uu____21395 g_when
                                                      in
                                                   (uu____21393, uu____21394)
                                               | (FStar_Pervasives_Native.None
                                                  ,FStar_Pervasives_Native.Some
                                                  w) ->
                                                   let g_w =
                                                     FStar_TypeChecker_Common.NonTrivial
                                                       w
                                                      in
                                                   let g =
                                                     FStar_TypeChecker_Env.guard_of_guard_formula
                                                       g_w
                                                      in
                                                   let uu____21413 =
                                                     FStar_TypeChecker_Util.weaken_precondition
                                                       env c1 g_w
                                                      in
                                                   (uu____21413, g_when)
                                                in
                                             (match uu____21309 with
                                              | (c_weak,g_when_weak) ->
                                                  let binders =
                                                    FStar_List.map
                                                      FStar_Syntax_Syntax.mk_binder
                                                      pat_bvs1
                                                     in
                                                  let maybe_return_c_weak
                                                    should_return1 =
                                                    let c_weak1 =
                                                      let uu____21456 =
                                                        should_return1 &&
                                                          (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                             c_weak)
                                                         in
                                                      if uu____21456
                                                      then
                                                        FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                          env branch_exp1
                                                          c_weak
                                                      else c_weak  in
                                                    FStar_TypeChecker_Util.close_lcomp
                                                      env pat_bvs1 c_weak1
                                                     in
                                                  let uu____21461 =
                                                    FStar_TypeChecker_Env.close_guard
                                                      env binders g_when_weak
                                                     in
                                                  let uu____21462 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      guard_pat g_branch1
                                                     in
                                                  ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                    (c_weak.FStar_TypeChecker_Common.cflags),
                                                    maybe_return_c_weak,
                                                    uu____21461, uu____21462))
                                          in
                                       match uu____21214 with
                                       | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                           ->
                                           let branch_guard =
                                             let uu____21513 =
                                               let uu____21515 =
                                                 FStar_TypeChecker_Env.should_verify
                                                   env
                                                  in
                                               Prims.op_Negation uu____21515
                                                in
                                             if uu____21513
                                             then FStar_Syntax_Util.t_true
                                             else
                                               (let rec build_branch_guard
                                                  scrutinee_tm1 pattern2
                                                  pat_exp1 =
                                                  let discriminate
                                                    scrutinee_tm2 f =
                                                    let uu____21569 =
                                                      let uu____21577 =
                                                        FStar_TypeChecker_Env.typ_of_datacon
                                                          env
                                                          f.FStar_Syntax_Syntax.v
                                                         in
                                                      FStar_TypeChecker_Env.datacons_of_typ
                                                        env uu____21577
                                                       in
                                                    match uu____21569 with
                                                    | (is_induc,datacons) ->
                                                        if
                                                          (Prims.op_Negation
                                                             is_induc)
                                                            ||
                                                            ((FStar_List.length
                                                                datacons)
                                                               >
                                                               Prims.int_one)
                                                        then
                                                          let discriminator =
                                                            FStar_Syntax_Util.mk_discriminator
                                                              f.FStar_Syntax_Syntax.v
                                                             in
                                                          let uu____21593 =
                                                            FStar_TypeChecker_Env.try_lookup_lid
                                                              env
                                                              discriminator
                                                             in
                                                          (match uu____21593
                                                           with
                                                           | FStar_Pervasives_Native.None
                                                                -> []
                                                           | uu____21614 ->
                                                               let disc =
                                                                 FStar_Syntax_Syntax.fvar
                                                                   discriminator
                                                                   (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                   FStar_Pervasives_Native.None
                                                                  in
                                                               let disc1 =
                                                                 let uu____21630
                                                                   =
                                                                   let uu____21635
                                                                    =
                                                                    let uu____21636
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                    [uu____21636]
                                                                     in
                                                                   FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____21635
                                                                    in
                                                                 uu____21630
                                                                   FStar_Pervasives_Native.None
                                                                   scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let uu____21661
                                                                 =
                                                                 FStar_Syntax_Util.mk_eq2
                                                                   FStar_Syntax_Syntax.U_zero
                                                                   FStar_Syntax_Util.t_bool
                                                                   disc1
                                                                   FStar_Syntax_Util.exp_true_bool
                                                                  in
                                                               [uu____21661])
                                                        else []
                                                     in
                                                  let fail1 uu____21669 =
                                                    let uu____21670 =
                                                      let uu____21672 =
                                                        FStar_Range.string_of_range
                                                          pat_exp1.FStar_Syntax_Syntax.pos
                                                         in
                                                      let uu____21674 =
                                                        FStar_Syntax_Print.term_to_string
                                                          pat_exp1
                                                         in
                                                      let uu____21676 =
                                                        FStar_Syntax_Print.tag_of_term
                                                          pat_exp1
                                                         in
                                                      FStar_Util.format3
                                                        "tc_eqn: Impossible (%s) %s (%s)"
                                                        uu____21672
                                                        uu____21674
                                                        uu____21676
                                                       in
                                                    failwith uu____21670  in
                                                  let rec head_constructor t
                                                    =
                                                    match t.FStar_Syntax_Syntax.n
                                                    with
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        fv.FStar_Syntax_Syntax.fv_name
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        (t1,uu____21691) ->
                                                        head_constructor t1
                                                    | uu____21696 -> fail1 ()
                                                     in
                                                  let force_scrutinee
                                                    uu____21702 =
                                                    match scrutinee_tm1 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____21703 =
                                                          let uu____21705 =
                                                            FStar_Range.string_of_range
                                                              pattern2.FStar_Syntax_Syntax.p
                                                             in
                                                          let uu____21707 =
                                                            FStar_Syntax_Print.pat_to_string
                                                              pattern2
                                                             in
                                                          FStar_Util.format2
                                                            "Impossible (%s): scrutinee of match is not defined %s"
                                                            uu____21705
                                                            uu____21707
                                                           in
                                                        failwith uu____21703
                                                    | FStar_Pervasives_Native.Some
                                                        t -> t
                                                     in
                                                  let pat_exp2 =
                                                    let uu____21714 =
                                                      FStar_Syntax_Subst.compress
                                                        pat_exp1
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____21714
                                                      FStar_Syntax_Util.unmeta
                                                     in
                                                  match ((pattern2.FStar_Syntax_Syntax.v),
                                                          (pat_exp2.FStar_Syntax_Syntax.n))
                                                  with
                                                  | (uu____21719,FStar_Syntax_Syntax.Tm_name
                                                     uu____21720) -> []
                                                  | (uu____21721,FStar_Syntax_Syntax.Tm_constant
                                                     (FStar_Const.Const_unit
                                                     )) -> []
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     _c,FStar_Syntax_Syntax.Tm_constant
                                                     c1) ->
                                                      let uu____21724 =
                                                        let uu____21725 =
                                                          tc_constant env
                                                            pat_exp2.FStar_Syntax_Syntax.pos
                                                            c1
                                                           in
                                                        let uu____21726 =
                                                          force_scrutinee ()
                                                           in
                                                        FStar_Syntax_Util.mk_eq2
                                                          FStar_Syntax_Syntax.U_zero
                                                          uu____21725
                                                          uu____21726
                                                          pat_exp2
                                                         in
                                                      [uu____21724]
                                                  | (FStar_Syntax_Syntax.Pat_constant
                                                     (FStar_Const.Const_int
                                                     (uu____21727,FStar_Pervasives_Native.Some
                                                      uu____21728)),uu____21729)
                                                      ->
                                                      let uu____21746 =
                                                        let uu____21753 =
                                                          FStar_TypeChecker_Env.clear_expected_typ
                                                            env
                                                           in
                                                        match uu____21753
                                                        with
                                                        | (env1,uu____21767)
                                                            ->
                                                            env1.FStar_TypeChecker_Env.type_of
                                                              env1 pat_exp2
                                                         in
                                                      (match uu____21746 with
                                                       | (uu____21774,t,uu____21776)
                                                           ->
                                                           let uu____21777 =
                                                             let uu____21778
                                                               =
                                                               force_scrutinee
                                                                 ()
                                                                in
                                                             FStar_Syntax_Util.mk_eq2
                                                               FStar_Syntax_Syntax.U_zero
                                                               t uu____21778
                                                               pat_exp2
                                                              in
                                                           [uu____21777])
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21779,[]),FStar_Syntax_Syntax.Tm_uinst
                                                     uu____21780) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21804 =
                                                        let uu____21806 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21806
                                                         in
                                                      if uu____21804
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21816 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21819 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21816
                                                           uu____21819)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21822,[]),FStar_Syntax_Syntax.Tm_fvar
                                                     uu____21823) ->
                                                      let f =
                                                        head_constructor
                                                          pat_exp2
                                                         in
                                                      let uu____21841 =
                                                        let uu____21843 =
                                                          FStar_TypeChecker_Env.is_datacon
                                                            env
                                                            f.FStar_Syntax_Syntax.v
                                                           in
                                                        Prims.op_Negation
                                                          uu____21843
                                                         in
                                                      if uu____21841
                                                      then
                                                        failwith
                                                          "Impossible: nullary patterns must be data constructors"
                                                      else
                                                        (let uu____21853 =
                                                           force_scrutinee ()
                                                            in
                                                         let uu____21856 =
                                                           head_constructor
                                                             pat_exp2
                                                            in
                                                         discriminate
                                                           uu____21853
                                                           uu____21856)
                                                  | (FStar_Syntax_Syntax.Pat_cons
                                                     (uu____21859,pat_args),FStar_Syntax_Syntax.Tm_app
                                                     (head1,args)) ->
                                                      let f =
                                                        head_constructor
                                                          head1
                                                         in
                                                      let uu____21906 =
                                                        (let uu____21910 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____21910)
                                                          ||
                                                          ((FStar_List.length
                                                              pat_args)
                                                             <>
                                                             (FStar_List.length
                                                                args))
                                                         in
                                                      if uu____21906
                                                      then
                                                        failwith
                                                          "Impossible: application patterns must be fully-applied data constructors"
                                                      else
                                                        (let sub_term_guards
                                                           =
                                                           let uu____21938 =
                                                             let uu____21943
                                                               =
                                                               FStar_List.zip
                                                                 pat_args
                                                                 args
                                                                in
                                                             FStar_All.pipe_right
                                                               uu____21943
                                                               (FStar_List.mapi
                                                                  (fun i  ->
                                                                    fun
                                                                    uu____22029
                                                                     ->
                                                                    match uu____22029
                                                                    with
                                                                    | 
                                                                    ((pi,uu____22051),
                                                                    (ei,uu____22053))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____22081
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____22081
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____22102
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____22114
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____22114
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____22116
                                                                    =
                                                                    let uu____22117
                                                                    =
                                                                    let uu____22122
                                                                    =
                                                                    let uu____22123
                                                                    =
                                                                    let uu____22132
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____22132
                                                                     in
                                                                    [uu____22123]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____22122
                                                                     in
                                                                    uu____22117
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____22116
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____21938
                                                             FStar_List.flatten
                                                            in
                                                         let uu____22155 =
                                                           let uu____22158 =
                                                             force_scrutinee
                                                               ()
                                                              in
                                                           discriminate
                                                             uu____22158 f
                                                            in
                                                         FStar_List.append
                                                           uu____22155
                                                           sub_term_guards)
                                                  | (FStar_Syntax_Syntax.Pat_dot_term
                                                     uu____22161,uu____22162)
                                                      -> []
                                                  | uu____22169 ->
                                                      let uu____22174 =
                                                        let uu____22176 =
                                                          FStar_Syntax_Print.pat_to_string
                                                            pattern2
                                                           in
                                                        let uu____22178 =
                                                          FStar_Syntax_Print.term_to_string
                                                            pat_exp2
                                                           in
                                                        FStar_Util.format2
                                                          "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                          uu____22176
                                                          uu____22178
                                                         in
                                                      failwith uu____22174
                                                   in
                                                let build_and_check_branch_guard
                                                  scrutinee_tm1 pattern2 pat
                                                  =
                                                  let uu____22207 =
                                                    let uu____22209 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env
                                                       in
                                                    Prims.op_Negation
                                                      uu____22209
                                                     in
                                                  if uu____22207
                                                  then
                                                    FStar_TypeChecker_Util.fvar_const
                                                      env
                                                      FStar_Parser_Const.true_lid
                                                  else
                                                    (let t =
                                                       let uu____22215 =
                                                         build_branch_guard
                                                           scrutinee_tm1
                                                           pattern2 pat
                                                          in
                                                       FStar_All.pipe_left
                                                         FStar_Syntax_Util.mk_conj_l
                                                         uu____22215
                                                        in
                                                     let uu____22224 =
                                                       FStar_Syntax_Util.type_u
                                                         ()
                                                        in
                                                     match uu____22224 with
                                                     | (k,uu____22230) ->
                                                         let uu____22231 =
                                                           tc_check_tot_or_gtot_term
                                                             scrutinee_env t
                                                             k
                                                            in
                                                         (match uu____22231
                                                          with
                                                          | (t1,uu____22239,uu____22240)
                                                              -> t1))
                                                   in
                                                let branch_guard =
                                                  build_and_check_branch_guard
                                                    (FStar_Pervasives_Native.Some
                                                       scrutinee_tm) pattern1
                                                    norm_pat_exp
                                                   in
                                                let branch_guard1 =
                                                  match when_condition with
                                                  | FStar_Pervasives_Native.None
                                                       -> branch_guard
                                                  | FStar_Pervasives_Native.Some
                                                      w ->
                                                      FStar_Syntax_Util.mk_conj
                                                        branch_guard w
                                                   in
                                                branch_guard1)
                                              in
                                           let guard =
                                             FStar_TypeChecker_Env.conj_guard
                                               g_when1 g_branch1
                                              in
                                           ((let uu____22252 =
                                               FStar_TypeChecker_Env.debug
                                                 env FStar_Options.High
                                                in
                                             if uu____22252
                                             then
                                               let uu____22255 =
                                                 FStar_TypeChecker_Rel.guard_to_string
                                                   env guard
                                                  in
                                               FStar_All.pipe_left
                                                 (FStar_Util.print1
                                                    "Carrying guard from match: %s\n")
                                                 uu____22255
                                             else ());
                                            (let uu____22261 =
                                               FStar_Syntax_Subst.close_branch
                                                 (pattern1, when_clause1,
                                                   branch_exp1)
                                                in
                                             let uu____22278 =
                                               let uu____22279 =
                                                 FStar_List.map
                                                   FStar_Syntax_Syntax.mk_binder
                                                   pat_bvs1
                                                  in
                                               FStar_TypeChecker_Util.close_guard_implicits
                                                 env uu____22279 guard
                                                in
                                             (uu____22261, branch_guard,
                                               effect_label, cflags,
                                               maybe_return_c, uu____22278))))))))))

and (check_top_level_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let uu____22326 = check_let_bound_def true env1 lb  in
          (match uu____22326 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____22352 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____22374 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____22374, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____22380 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____22380
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____22381 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____22381 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____22399 =
                          let uu____22412 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____22412  in
                        (match uu____22399 with
                         | (uu____22462,univs1,e11,c11,gvs) ->
                             let g13 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.map_guard g12)
                                 (FStar_TypeChecker_Normalize.normalize
                                    [FStar_TypeChecker_Env.Beta;
                                    FStar_TypeChecker_Env.DoNotUnfoldPureLets;
                                    FStar_TypeChecker_Env.CompressUvars;
                                    FStar_TypeChecker_Env.NoFullNorm;
                                    FStar_TypeChecker_Env.Exclude
                                      FStar_TypeChecker_Env.Zeta] env1)
                                in
                             let g14 =
                               FStar_TypeChecker_Env.abstract_guard_n gvs g13
                                in
                             let uu____22476 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs1, uu____22476)))
                  in
               (match uu____22352 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____22493 =
                      let uu____22502 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____22502
                      then
                        let uu____22513 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____22513 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____22547 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____22547
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____22548 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____22548, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____22560 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____22560 with
                          | (comp1,g_comp1) ->
                              (FStar_TypeChecker_Rel.force_trivial_guard env1
                                 g_comp1;
                               (let c =
                                  FStar_All.pipe_right comp1
                                    (FStar_TypeChecker_Normalize.normalize_comp
                                       [FStar_TypeChecker_Env.Beta;
                                       FStar_TypeChecker_Env.NoFullNorm;
                                       FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                       env1)
                                   in
                                let e21 =
                                  let uu____22584 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____22584
                                  then e2
                                  else
                                    ((let uu____22592 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____22592
                                        FStar_TypeChecker_Err.top_level_effect);
                                     FStar_Syntax_Syntax.mk
                                       (FStar_Syntax_Syntax.Tm_meta
                                          (e2,
                                            (FStar_Syntax_Syntax.Meta_desugared
                                               FStar_Syntax_Syntax.Masked_effect)))
                                       FStar_Pervasives_Native.None
                                       e2.FStar_Syntax_Syntax.pos)
                                   in
                                (e21, c)))))
                       in
                    (match uu____22493 with
                     | (e21,c12) ->
                         ((let uu____22616 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____22616
                           then
                             let uu____22619 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____22619
                           else ());
                          (let e12 =
                             let uu____22625 = FStar_Options.tcnorm ()  in
                             if uu____22625
                             then
                               FStar_TypeChecker_Normalize.normalize
                                 [FStar_TypeChecker_Env.UnfoldAttr
                                    [FStar_Parser_Const.tcnorm_attr];
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Beta;
                                 FStar_TypeChecker_Env.Exclude
                                   FStar_TypeChecker_Env.Zeta;
                                 FStar_TypeChecker_Env.NoFullNorm;
                                 FStar_TypeChecker_Env.DoNotUnfoldPureLets]
                                 env1 e11
                             else e11  in
                           (let uu____22631 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____22631
                            then
                              let uu____22634 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____22634
                            else ());
                           (let cres =
                              let uu____22640 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____22640
                              then
                                FStar_Syntax_Syntax.mk_Total'
                                  FStar_Syntax_Syntax.t_unit
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.U_zero)
                              else
                                (let c1_comp_typ =
                                   FStar_All.pipe_right c12
                                     (FStar_TypeChecker_Env.unfold_effect_abbrev
                                        env1)
                                    in
                                 let c1_wp =
                                   match c1_comp_typ.FStar_Syntax_Syntax.effect_args
                                   with
                                   | (wp,uu____22648)::[] -> wp
                                   | uu____22673 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args"
                                    in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name
                                    in
                                 let wp2 =
                                   let uu____22689 =
                                     let uu____22694 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl
                                         c1_eff_decl.FStar_Syntax_Syntax.ret_wp
                                        in
                                     let uu____22695 =
                                       let uu____22696 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____22705 =
                                         let uu____22716 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____22716]  in
                                       uu____22696 :: uu____22705  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____22694 uu____22695
                                      in
                                   uu____22689 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let uu____22752 =
                                     let uu____22757 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl
                                         c1_eff_decl.FStar_Syntax_Syntax.bind_wp
                                        in
                                     let uu____22758 =
                                       let uu____22759 =
                                         let uu____22768 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____22768
                                          in
                                       let uu____22777 =
                                         let uu____22788 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____22805 =
                                           let uu____22816 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____22825 =
                                             let uu____22836 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____22845 =
                                               let uu____22856 =
                                                 let uu____22865 =
                                                   let uu____22866 =
                                                     let uu____22867 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____22867]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____22866 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____22865
                                                  in
                                               [uu____22856]  in
                                             uu____22836 :: uu____22845  in
                                           uu____22816 :: uu____22825  in
                                         uu____22788 :: uu____22805  in
                                       uu____22759 :: uu____22777  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____22757 uu____22758
                                      in
                                   uu____22752 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____22944 =
                                   let uu____22945 =
                                     let uu____22956 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____22956]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____22945;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____22944)
                               in
                            let lb1 =
                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                FStar_Pervasives_Native.None
                                lb.FStar_Syntax_Syntax.lbname univ_vars2
                                (FStar_Syntax_Util.comp_result c12)
                                (FStar_Syntax_Util.comp_effect_name c12) e12
                                lb.FStar_Syntax_Syntax.lbattrs
                                lb.FStar_Syntax_Syntax.lbpos
                               in
                            let uu____22984 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____22998 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____22984, uu____22998,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____22999 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____23010 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____23010
        then
          let universe_of_binders bs =
            let uu____23037 =
              FStar_List.fold_left
                (fun uu____23062  ->
                   fun b  ->
                     match uu____23062 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____23037 with | (uu____23110,us) -> FStar_List.rev us
             in
          let quant =
            FStar_Syntax_Util.smt_lemma_as_forall lem_typ universe_of_binders
             in
          FStar_TypeChecker_Util.weaken_precondition env c2
            (FStar_TypeChecker_Common.NonTrivial quant)
        else c2

and (check_inner_let :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let env1 = instantiate_both env  in
      match e.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),e2) ->
          let env2 =
            let uu___2981_23146 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___2981_23146.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___2981_23146.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___2981_23146.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___2981_23146.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___2981_23146.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___2981_23146.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___2981_23146.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___2981_23146.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___2981_23146.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___2981_23146.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___2981_23146.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___2981_23146.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___2981_23146.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___2981_23146.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___2981_23146.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___2981_23146.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___2981_23146.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___2981_23146.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___2981_23146.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___2981_23146.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___2981_23146.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___2981_23146.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___2981_23146.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___2981_23146.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___2981_23146.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___2981_23146.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___2981_23146.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___2981_23146.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___2981_23146.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___2981_23146.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___2981_23146.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___2981_23146.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___2981_23146.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___2981_23146.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___2981_23146.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___2981_23146.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___2981_23146.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___2981_23146.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___2981_23146.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___2981_23146.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___2981_23146.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___2981_23146.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___2981_23146.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let uu____23148 =
            let uu____23160 =
              let uu____23161 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____23161 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____23160 lb  in
          (match uu____23148 with
           | (e1,uu____23184,c1,g1,annotated) ->
               let pure_or_ghost =
                 FStar_TypeChecker_Common.is_pure_or_ghost_lcomp c1  in
               let is_inline_let =
                 FStar_Util.for_some
                   (FStar_Syntax_Util.is_fvar
                      FStar_Parser_Const.inline_let_attr)
                   lb.FStar_Syntax_Syntax.lbattrs
                  in
               (if is_inline_let && (Prims.op_Negation pure_or_ghost)
                then
                  (let uu____23198 =
                     let uu____23204 =
                       let uu____23206 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____23208 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____23206 uu____23208
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____23204)
                      in
                   FStar_Errors.raise_error uu____23198
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____23219 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____23219
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___2996_23231 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2996_23231.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2996_23231.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____23232 =
                   let uu____23237 =
                     let uu____23238 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____23238]  in
                   FStar_Syntax_Subst.open_term uu____23237 e2  in
                 match uu____23232 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____23282 = tc_term env_x e21  in
                     (match uu____23282 with
                      | (e22,c2,g2) ->
                          let c21 =
                            maybe_intro_smt_lemma env_x
                              c1.FStar_TypeChecker_Common.res_typ c2
                             in
                          let cres =
                            FStar_TypeChecker_Util.maybe_return_e2_and_bind
                              e1.FStar_Syntax_Syntax.pos env2
                              (FStar_Pervasives_Native.Some e1) c1 e22
                              ((FStar_Pervasives_Native.Some x1), c21)
                             in
                          let e11 =
                            FStar_TypeChecker_Util.maybe_lift env2 e1
                              c1.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c1.FStar_TypeChecker_Common.res_typ
                             in
                          let e23 =
                            FStar_TypeChecker_Util.maybe_lift env2 e22
                              c21.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.eff_name
                              c21.FStar_TypeChecker_Common.res_typ
                             in
                          let lb1 =
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Util.Inl x1) []
                              c1.FStar_TypeChecker_Common.res_typ
                              cres.FStar_TypeChecker_Common.eff_name e11
                              attrs lb.FStar_Syntax_Syntax.lbpos
                             in
                          let e3 =
                            let uu____23308 =
                              let uu____23315 =
                                let uu____23316 =
                                  let uu____23330 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____23330)  in
                                FStar_Syntax_Syntax.Tm_let uu____23316  in
                              FStar_Syntax_Syntax.mk uu____23315  in
                            uu____23308 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let x_eq_e1 =
                            let uu____23348 =
                              let uu____23349 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_TypeChecker_Common.res_typ
                                 in
                              let uu____23350 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____23349
                                c1.FStar_TypeChecker_Common.res_typ
                                uu____23350 e11
                               in
                            FStar_All.pipe_left
                              (fun _23351  ->
                                 FStar_TypeChecker_Common.NonTrivial _23351)
                              uu____23348
                             in
                          let g21 =
                            let uu____23353 =
                              let uu____23354 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____23354 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____23353
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____23357 =
                            let uu____23359 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____23359  in
                          if uu____23357
                          then
                            let tt =
                              let uu____23370 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____23370
                                FStar_Option.get
                               in
                            ((let uu____23376 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____23376
                              then
                                let uu____23381 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____23383 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____23381 uu____23383
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____23390 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____23390 with
                             | (t,g_ex) ->
                                 ((let uu____23404 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____23404
                                   then
                                     let uu____23409 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____23411 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____23409 uu____23411
                                   else ());
                                  (let uu____23416 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3029_23418 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3029_23418.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3029_23418.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3029_23418.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____23416))))))))
      | uu____23419 ->
          failwith "Impossible (inner let with more than one lb)"

and (check_top_level_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____23455 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____23455 with
           | (lbs1,e21) ->
               let uu____23474 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____23474 with
                | (env0,topt) ->
                    let uu____23493 = build_let_rec_env true env0 lbs1  in
                    (match uu____23493 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____23516 = check_let_recs rec_env lbs2  in
                         (match uu____23516 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____23536 =
                                  let uu____23537 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____23537
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____23536
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____23543 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____23543
                                  (fun _23560  ->
                                     FStar_Pervasives_Native.Some _23560)
                                 in
                              let lbs4 =
                                if
                                  Prims.op_Negation
                                    env1.FStar_TypeChecker_Env.generalize
                                then
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          let lbdef =
                                            FStar_TypeChecker_Normalize.reduce_uvar_solutions
                                              env1
                                              lb.FStar_Syntax_Syntax.lbdef
                                             in
                                          if
                                            lb.FStar_Syntax_Syntax.lbunivs =
                                              []
                                          then lb
                                          else
                                            FStar_Syntax_Util.close_univs_and_mk_letbinding
                                              all_lb_names
                                              lb.FStar_Syntax_Syntax.lbname
                                              lb.FStar_Syntax_Syntax.lbunivs
                                              lb.FStar_Syntax_Syntax.lbtyp
                                              lb.FStar_Syntax_Syntax.lbeff
                                              lbdef
                                              lb.FStar_Syntax_Syntax.lbattrs
                                              lb.FStar_Syntax_Syntax.lbpos))
                                else
                                  (let ecs =
                                     let uu____23597 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____23631 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____23631)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____23597
                                      in
                                   FStar_List.map2
                                     (fun uu____23666  ->
                                        fun lb  ->
                                          match uu____23666 with
                                          | (x,uvs,e,c,gvs) ->
                                              FStar_Syntax_Util.close_univs_and_mk_letbinding
                                                all_lb_names x uvs
                                                (FStar_Syntax_Util.comp_result
                                                   c)
                                                (FStar_Syntax_Util.comp_effect_name
                                                   c) e
                                                lb.FStar_Syntax_Syntax.lbattrs
                                                lb.FStar_Syntax_Syntax.lbpos)
                                     ecs lbs3)
                                 in
                              let cres =
                                let uu____23714 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____23714
                                 in
                              let uu____23715 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____23715 with
                               | (lbs5,e22) ->
                                   ((let uu____23735 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____23735
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____23736 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____23736, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____23750 -> failwith "Impossible"

and (check_inner_let_rec :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun top  ->
      let env1 = instantiate_both env  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_let ((true ,lbs),e2) ->
          let uu____23786 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____23786 with
           | (lbs1,e21) ->
               let uu____23805 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____23805 with
                | (env0,topt) ->
                    let uu____23824 = build_let_rec_env false env0 lbs1  in
                    (match uu____23824 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____23847 =
                           let uu____23854 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____23854
                             (fun uu____23877  ->
                                match uu____23877 with
                                | (lbs3,g) ->
                                    let uu____23896 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____23896))
                            in
                         (match uu____23847 with
                          | (lbs3,g_lbs) ->
                              let uu____23911 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3104_23934 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3104_23934.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3104_23934.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3107_23936 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3107_23936.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3107_23936.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3107_23936.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3107_23936.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3107_23936.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3107_23936.FStar_Syntax_Syntax.lbpos)
                                            }  in
                                          let env3 =
                                            FStar_TypeChecker_Env.push_let_binding
                                              env2
                                              lb1.FStar_Syntax_Syntax.lbname
                                              ([],
                                                (lb1.FStar_Syntax_Syntax.lbtyp))
                                             in
                                          (env3, lb1)) env1)
                                 in
                              (match uu____23911 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____23963 = tc_term env2 e21  in
                                   (match uu____23963 with
                                    | (e22,cres,g2) ->
                                        let cres1 =
                                          FStar_List.fold_right
                                            (fun lb  ->
                                               fun cres1  ->
                                                 maybe_intro_smt_lemma env2
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                   cres1) lbs4 cres
                                           in
                                        let cres2 =
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env2 e22 cres1
                                           in
                                        let cres3 =
                                          FStar_TypeChecker_Common.lcomp_set_flags
                                            cres2
                                            [FStar_Syntax_Syntax.SHOULD_NOT_INLINE]
                                           in
                                        let guard =
                                          let uu____23987 =
                                            let uu____23988 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____23988 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____23987
                                           in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_lcomp
                                            env2 bvs cres3
                                           in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ
                                           in
                                        let cres5 =
                                          let uu___3128_23998 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3128_23998.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3128_23998.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3128_23998.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____24006 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____24006))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____24007 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____24007 with
                                         | (lbs5,e23) ->
                                             let e =
                                               FStar_Syntax_Syntax.mk
                                                 (FStar_Syntax_Syntax.Tm_let
                                                    ((true, lbs5), e23))
                                                 FStar_Pervasives_Native.None
                                                 top.FStar_Syntax_Syntax.pos
                                                in
                                             (match topt with
                                              | FStar_Pervasives_Native.Some
                                                  uu____24048 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____24049 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____24049 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3144_24063
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3144_24063.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3144_24063.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3144_24063.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____24064 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____24064))))))))))
      | uu____24065 -> failwith "Impossible"

and (build_let_rec_env :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Syntax_Syntax.letbinding Prims.list *
          FStar_TypeChecker_Env.env_t * FStar_TypeChecker_Common.guard_t))
  =
  fun top_level  ->
    fun env  ->
      fun lbs  ->
        let env0 = env  in
        let termination_check_enabled lbname lbdef lbtyp =
          let uu____24113 = FStar_Options.ml_ish ()  in
          if uu____24113
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____24121 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____24121 with
             | (formals,c) ->
                 let uu____24153 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____24153 with
                  | (actuals,uu____24164,uu____24165) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____24186 =
                          let uu____24192 =
                            let uu____24194 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____24196 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____24194 uu____24196
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____24192)
                           in
                        FStar_Errors.raise_error uu____24186
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____24204 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____24204 actuals
                            in
                         if
                           (FStar_List.length formals) <>
                             (FStar_List.length actuals1)
                         then
                           (let actuals_msg =
                              let n1 = FStar_List.length actuals1  in
                              if n1 = Prims.int_one
                              then "1 argument was found"
                              else
                                (let uu____24235 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____24235)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____24254 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____24254)
                               in
                            let msg =
                              let uu____24259 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____24261 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____24259 uu____24261 formals_msg
                                actuals_msg
                               in
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_LetRecArgumentMismatch,
                                msg) lbdef.FStar_Syntax_Syntax.pos)
                         else ();
                         (let quals =
                            FStar_TypeChecker_Env.lookup_effect_quals env
                              (FStar_Syntax_Util.comp_effect_name c)
                             in
                          FStar_All.pipe_right quals
                            (FStar_List.contains
                               FStar_Syntax_Syntax.TotalEffect)))))
           in
        let uu____24273 =
          FStar_List.fold_left
            (fun uu____24306  ->
               fun lb  ->
                 match uu____24306 with
                 | (lbs1,env1,g_acc) ->
                     let uu____24331 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____24331 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____24354 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____24373 =
                                 let uu____24380 =
                                   let uu____24381 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____24381
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3190_24392 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3190_24392.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3190_24392.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3190_24392.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3190_24392.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3190_24392.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3190_24392.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3190_24392.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3190_24392.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3190_24392.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3190_24392.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3190_24392.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3190_24392.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3190_24392.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3190_24392.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3190_24392.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3190_24392.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3190_24392.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3190_24392.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3190_24392.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3190_24392.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3190_24392.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3190_24392.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3190_24392.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3190_24392.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3190_24392.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3190_24392.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3190_24392.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3190_24392.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3190_24392.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3190_24392.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3190_24392.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3190_24392.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3190_24392.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3190_24392.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3190_24392.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3190_24392.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3190_24392.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3190_24392.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3190_24392.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3190_24392.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3190_24392.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3190_24392.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3190_24392.FStar_TypeChecker_Env.strict_args_tab)
                                    }) t uu____24380
                                  in
                               match uu____24373 with
                               | (t1,uu____24401,g) ->
                                   let uu____24403 =
                                     let uu____24404 =
                                       let uu____24405 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____24405
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____24404
                                      in
                                   let uu____24406 = norm env01 t1  in
                                   (uu____24403, uu____24406))
                             in
                          (match uu____24354 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____24426 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____24426
                                 then
                                   let uu___3200_24429 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3200_24429.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3200_24429.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3200_24429.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3200_24429.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3200_24429.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3200_24429.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3200_24429.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3200_24429.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3200_24429.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3200_24429.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3200_24429.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3200_24429.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3200_24429.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3200_24429.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3200_24429.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3200_24429.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3200_24429.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3200_24429.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3200_24429.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3200_24429.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3200_24429.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3200_24429.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3200_24429.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3200_24429.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3200_24429.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3200_24429.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3200_24429.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3200_24429.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3200_24429.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3200_24429.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3200_24429.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3200_24429.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3200_24429.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3200_24429.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3200_24429.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3200_24429.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3200_24429.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3200_24429.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3200_24429.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3200_24429.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3200_24429.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3200_24429.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3200_24429.FStar_TypeChecker_Env.strict_args_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3203_24443 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3203_24443.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3203_24443.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3203_24443.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3203_24443.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____24273 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____24469 =
        let uu____24478 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____24504 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____24504 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____24534 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____24534
                       | uu____24541 ->
                           let lb1 =
                             let uu___3220_24544 = lb  in
                             let uu____24545 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3220_24544.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3220_24544.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3220_24544.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3220_24544.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____24545;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3220_24544.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3220_24544.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____24548 =
                             let uu____24555 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____24555
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____24548 with
                            | (e,c,g) ->
                                ((let uu____24564 =
                                    let uu____24566 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____24566  in
                                  if uu____24564
                                  then
                                    FStar_Errors.raise_error
                                      (FStar_Errors.Fatal_UnexpectedGTotForLetRec,
                                        "Expected let rec to be a Tot term; got effect GTot")
                                      e.FStar_Syntax_Syntax.pos
                                  else ());
                                 (let lb2 =
                                    FStar_Syntax_Util.mk_letbinding
                                      lb1.FStar_Syntax_Syntax.lbname
                                      lb1.FStar_Syntax_Syntax.lbunivs
                                      lb1.FStar_Syntax_Syntax.lbtyp
                                      FStar_Parser_Const.effect_Tot_lid e
                                      lb1.FStar_Syntax_Syntax.lbattrs
                                      lb1.FStar_Syntax_Syntax.lbpos
                                     in
                                  (lb2, g)))))))
           in
        FStar_All.pipe_right uu____24478 FStar_List.unzip  in
      match uu____24469 with
      | (lbs1,gs) ->
          let g_lbs =
            FStar_List.fold_right FStar_TypeChecker_Env.conj_guard gs
              FStar_TypeChecker_Env.trivial_guard
             in
          (lbs1, g_lbs)

and (check_let_bound_def :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.univ_names *
          FStar_TypeChecker_Common.lcomp * FStar_TypeChecker_Common.guard_t *
          Prims.bool))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let uu____24622 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____24622 with
        | (env1,uu____24641) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____24649 = check_lbtyp top_level env lb  in
            (match uu____24649 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____24698 =
                     tc_maybe_toplevel_term
                       (let uu___3251_24707 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3251_24707.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3251_24707.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3251_24707.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3251_24707.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3251_24707.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3251_24707.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3251_24707.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3251_24707.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3251_24707.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3251_24707.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3251_24707.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3251_24707.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3251_24707.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3251_24707.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3251_24707.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3251_24707.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3251_24707.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3251_24707.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3251_24707.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3251_24707.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3251_24707.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3251_24707.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3251_24707.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3251_24707.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3251_24707.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3251_24707.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3251_24707.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3251_24707.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3251_24707.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3251_24707.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3251_24707.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3251_24707.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3251_24707.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3251_24707.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3251_24707.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3251_24707.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3251_24707.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3251_24707.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3251_24707.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3251_24707.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3251_24707.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3251_24707.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3251_24707.FStar_TypeChecker_Env.strict_args_tab)
                        }) e11
                      in
                   match uu____24698 with
                   | (e12,c1,g1) ->
                       let uu____24722 =
                         let uu____24727 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____24733  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____24727 e12 c1 wf_annot
                          in
                       (match uu____24722 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____24750 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____24750
                              then
                                let uu____24753 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____24755 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____24757 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____24753 uu____24755 uu____24757
                              else ());
                             (e12, univ_vars1, c11, g11,
                               (FStar_Option.isSome topt)))))))

and (check_lbtyp :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.letbinding ->
        (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option *
          FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.univ_names *
          FStar_Syntax_Syntax.subst_elt Prims.list *
          FStar_TypeChecker_Env.env))
  =
  fun top_level  ->
    fun env  ->
      fun lb  ->
        let t = FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbtyp  in
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_unknown  ->
            let uu____24796 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24796 with
             | (univ_opening,univ_vars1) ->
                 let uu____24829 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____24829))
        | uu____24834 ->
            let uu____24835 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____24835 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____24885 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____24885)
                 else
                   (let uu____24892 = FStar_Syntax_Util.type_u ()  in
                    match uu____24892 with
                    | (k,uu____24912) ->
                        let uu____24913 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____24913 with
                         | (t2,uu____24935,g) ->
                             ((let uu____24938 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____24938
                               then
                                 let uu____24941 =
                                   let uu____24943 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____24943
                                    in
                                 let uu____24944 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____24941 uu____24944
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____24950 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____24950))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____24956  ->
      match uu____24956 with
      | (x,imp) ->
          let uu____24983 = FStar_Syntax_Util.type_u ()  in
          (match uu____24983 with
           | (tu,u) ->
               ((let uu____25005 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____25005
                 then
                   let uu____25008 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____25010 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____25012 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____25008 uu____25010 uu____25012
                 else ());
                (let uu____25017 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____25017 with
                 | (t,uu____25039,g) ->
                     let uu____25041 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____25057 = tc_tactic env tau  in
                           (match uu____25057 with
                            | (tau1,uu____25071,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____25075 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____25041 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3313_25110 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3313_25110.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3313_25110.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____25112 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____25112
                            then
                              let uu____25115 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____25119 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____25115
                                uu____25119
                            else ());
                           (let uu____25124 = push_binding env x1  in
                            (x1, uu____25124, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____25136 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____25136
       then
         let uu____25139 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____25139
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____25252 = tc_binder env1 b  in
             (match uu____25252 with
              | (b1,env',g,u) ->
                  let uu____25301 = aux env' bs2  in
                  (match uu____25301 with
                   | (bs3,env'1,g',us) ->
                       let uu____25362 =
                         let uu____25363 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____25363  in
                       ((b1 :: bs3), env'1, uu____25362, (u :: us))))
          in
       aux env bs)

and (tc_smt_pats :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list Prims.list * FStar_TypeChecker_Common.guard_t))
  =
  fun en  ->
    fun pats  ->
      let tc_args en1 args =
        FStar_List.fold_right
          (fun uu____25471  ->
             fun uu____25472  ->
               match (uu____25471, uu____25472) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____25564 = tc_term en1 t  in
                     match uu____25564 with
                     | (t1,uu____25584,g') ->
                         let uu____25586 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____25586)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____25640  ->
             match uu____25640 with
             | (pats1,g) ->
                 let uu____25667 = tc_args en p  in
                 (match uu____25667 with
                  | (args,g') ->
                      let uu____25680 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____25680))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____25693 = tc_maybe_toplevel_term env e  in
      match uu____25693 with
      | (e1,c,g) ->
          let uu____25709 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
             in
          if uu____25709
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let uu____25721 = FStar_TypeChecker_Common.lcomp_comp c  in
             match uu____25721 with
             | (c1,g_c) ->
                 let c2 = norm_c env c1  in
                 let uu____25735 =
                   let uu____25741 =
                     FStar_TypeChecker_Util.is_pure_effect env
                       (FStar_Syntax_Util.comp_effect_name c2)
                      in
                   if uu____25741
                   then
                     let uu____25749 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c2)
                        in
                     (uu____25749, false)
                   else
                     (let uu____25754 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Util.comp_result c2)
                         in
                      (uu____25754, true))
                    in
                 (match uu____25735 with
                  | (target_comp,allow_ghost) ->
                      let uu____25767 =
                        FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                      (match uu____25767 with
                       | FStar_Pervasives_Native.Some g' ->
                           let uu____25777 =
                             FStar_TypeChecker_Common.lcomp_of_comp
                               target_comp
                              in
                           let uu____25778 =
                             let uu____25779 =
                               FStar_TypeChecker_Env.conj_guard g_c g'  in
                             FStar_TypeChecker_Env.conj_guard g1 uu____25779
                              in
                           (e1, uu____25777, uu____25778)
                       | uu____25780 ->
                           if allow_ghost
                           then
                             let uu____25790 =
                               FStar_TypeChecker_Err.expected_ghost_expression
                                 e1 c2
                                in
                             FStar_Errors.raise_error uu____25790
                               e1.FStar_Syntax_Syntax.pos
                           else
                             (let uu____25804 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e1 c2
                                 in
                              FStar_Errors.raise_error uu____25804
                                e1.FStar_Syntax_Syntax.pos))))

and (tc_check_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
          FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let env1 = FStar_TypeChecker_Env.set_expected_typ env t  in
        tc_tot_or_gtot_term env1 e

and (tc_trivial_guard :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp))
  =
  fun env  ->
    fun t  ->
      let uu____25828 = tc_tot_or_gtot_term env t  in
      match uu____25828 with
      | (t1,c,g) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env g; (t1, c))

let (type_of_tot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      (let uu____25861 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____25861
       then
         let uu____25866 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____25866
       else ());
      (let env1 =
         let uu___3397_25872 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3397_25872.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3397_25872.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3397_25872.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3397_25872.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3397_25872.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3397_25872.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3397_25872.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3397_25872.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3397_25872.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3397_25872.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3397_25872.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3397_25872.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3397_25872.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3397_25872.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3397_25872.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3397_25872.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3397_25872.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3397_25872.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3397_25872.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3397_25872.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3397_25872.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3397_25872.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3397_25872.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3397_25872.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3397_25872.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3397_25872.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3397_25872.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3397_25872.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3397_25872.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3397_25872.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3397_25872.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3397_25872.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3397_25872.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3397_25872.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3397_25872.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3397_25872.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3397_25872.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3397_25872.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3397_25872.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3397_25872.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3397_25872.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3397_25872.FStar_TypeChecker_Env.strict_args_tab)
         }  in
       let uu____25880 =
         try
           (fun uu___3401_25894  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____25915) ->
             let uu____25918 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____25918
          in
       match uu____25880 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____25936 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____25936
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____25947 =
                let uu____25953 =
                  let uu____25955 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____25955
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____25953)
                 in
              let uu____25959 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____25947 uu____25959))
  
let level_of_type_fail :
  'Auu____25975 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____25975
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____25993 =
          let uu____25999 =
            let uu____26001 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____26001 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____25999)  in
        let uu____26005 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____25993 uu____26005
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____26039 =
            let uu____26040 = FStar_Syntax_Util.unrefine t1  in
            uu____26040.FStar_Syntax_Syntax.n  in
          match uu____26039 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____26044 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____26050 = FStar_Syntax_Util.type_u ()  in
                 match uu____26050 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3433_26058 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3433_26058.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3433_26058.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3433_26058.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3433_26058.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3433_26058.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3433_26058.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3433_26058.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3433_26058.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3433_26058.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3433_26058.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3433_26058.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3433_26058.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3433_26058.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3433_26058.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3433_26058.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3433_26058.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3433_26058.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3433_26058.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3433_26058.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3433_26058.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3433_26058.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3433_26058.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3433_26058.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3433_26058.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3433_26058.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3433_26058.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3433_26058.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3433_26058.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3433_26058.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3433_26058.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3433_26058.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3433_26058.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3433_26058.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3433_26058.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3433_26058.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3433_26058.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3433_26058.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3433_26058.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3433_26058.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3433_26058.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3433_26058.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3433_26058.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3433_26058.FStar_TypeChecker_Env.strict_args_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____26063 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____26063
                       | uu____26065 ->
                           FStar_TypeChecker_Rel.force_trivial_guard env1 g);
                      u))
           in
        aux true t
  
let rec (universe_of_aux :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun e  ->
      let uu____26082 =
        let uu____26083 = FStar_Syntax_Subst.compress e  in
        uu____26083.FStar_Syntax_Syntax.n  in
      match uu____26082 with
      | FStar_Syntax_Syntax.Tm_bvar uu____26086 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____26089 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____26113 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____26130) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____26175) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____26182 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____26182 with | ((uu____26191,t),uu____26193) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____26199 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____26199
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____26202,(FStar_Util.Inl t,uu____26204),uu____26205) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____26252,(FStar_Util.Inr c,uu____26254),uu____26255) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____26303 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____26312;
             FStar_Syntax_Syntax.vars = uu____26313;_},us)
          ->
          let uu____26319 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____26319 with
           | ((us',t),uu____26330) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____26337 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____26337)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____26356 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____26358 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____26367) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____26394 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____26394 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____26414  ->
                      match uu____26414 with
                      | (b,uu____26422) ->
                          let uu____26427 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____26427) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____26432 = universe_of_aux env res  in
                 level_of_type env res uu____26432  in
               let u_c =
                 FStar_All.pipe_right c1
                   (FStar_TypeChecker_Util.universe_of_comp env u_res)
                  in
               let u =
                 FStar_TypeChecker_Normalize.normalize_universe env
                   (FStar_Syntax_Syntax.U_max (u_c :: us))
                  in
               FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
                 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos)
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let rec type_of_head retry hd2 args1 =
            let hd3 = FStar_Syntax_Subst.compress hd2  in
            match hd3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_bvar uu____26543 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____26559 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____26597 ->
                let uu____26598 = universe_of_aux env hd3  in
                (uu____26598, args1)
            | FStar_Syntax_Syntax.Tm_name uu____26609 ->
                let uu____26610 = universe_of_aux env hd3  in
                (uu____26610, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____26621 ->
                let uu____26634 = universe_of_aux env hd3  in
                (uu____26634, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____26645 ->
                let uu____26652 = universe_of_aux env hd3  in
                (uu____26652, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____26663 ->
                let uu____26690 = universe_of_aux env hd3  in
                (uu____26690, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____26701 ->
                let uu____26708 = universe_of_aux env hd3  in
                (uu____26708, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____26719 ->
                let uu____26720 = universe_of_aux env hd3  in
                (uu____26720, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____26731 ->
                let uu____26746 = universe_of_aux env hd3  in
                (uu____26746, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____26757 ->
                let uu____26764 = universe_of_aux env hd3  in
                (uu____26764, args1)
            | FStar_Syntax_Syntax.Tm_type uu____26775 ->
                let uu____26776 = universe_of_aux env hd3  in
                (uu____26776, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____26787,hd4::uu____26789) ->
                let uu____26854 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____26854 with
                 | (uu____26869,uu____26870,hd5) ->
                     let uu____26888 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____26888 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____26945 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____26947 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____26947 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____27005 ->
                let uu____27006 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____27006 with
                 | (env1,uu____27028) ->
                     let env2 =
                       let uu___3594_27034 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3594_27034.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3594_27034.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3594_27034.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3594_27034.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3594_27034.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3594_27034.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3594_27034.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3594_27034.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3594_27034.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3594_27034.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3594_27034.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3594_27034.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3594_27034.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3594_27034.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3594_27034.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3594_27034.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3594_27034.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3594_27034.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3594_27034.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3594_27034.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3594_27034.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3594_27034.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3594_27034.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3594_27034.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3594_27034.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3594_27034.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3594_27034.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3594_27034.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3594_27034.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3594_27034.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3594_27034.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3594_27034.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3594_27034.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3594_27034.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3594_27034.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3594_27034.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3594_27034.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3594_27034.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3594_27034.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3594_27034.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3594_27034.FStar_TypeChecker_Env.strict_args_tab)
                       }  in
                     ((let uu____27039 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____27039
                       then
                         let uu____27044 =
                           let uu____27046 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____27046  in
                         let uu____27047 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____27044 uu____27047
                       else ());
                      (let uu____27052 = tc_term env2 hd3  in
                       match uu____27052 with
                       | (uu____27073,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____27074;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____27076;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____27077;_},g)
                           ->
                           ((let uu____27095 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____27095 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____27106 = type_of_head true hd1 args  in
          (match uu____27106 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____27145 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____27145 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____27197 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____27197)))
      | FStar_Syntax_Syntax.Tm_match (uu____27199,hd1::uu____27201) ->
          let uu____27266 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____27266 with
           | (uu____27267,uu____27268,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____27286,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____27333 = universe_of_aux env e  in
      level_of_type env e uu____27333
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____27357 = tc_binders env tps  in
      match uu____27357 with
      | (tps1,env1,g,us) ->
          (FStar_TypeChecker_Rel.force_trivial_guard env1 g; (tps1, env1, us))
  
let rec (type_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let mk_tm_type u =
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
         in
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____27415 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____27441 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27447 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____27447
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27449 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____27449
            (fun uu____27463  ->
               match uu____27463 with
               | (t2,uu____27471) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27473;
             FStar_Syntax_Syntax.vars = uu____27474;_},us)
          ->
          let uu____27480 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____27480
            (fun uu____27494  ->
               match uu____27494 with
               | (t2,uu____27502) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____27503) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____27505 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____27505
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____27507 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____27507
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____27512;_})
          ->
          let mk_comp =
            let uu____27556 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____27556
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____27587 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____27587
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____27657 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____27657
                 (fun u  ->
                    let uu____27665 =
                      let uu____27668 =
                        let uu____27675 =
                          let uu____27676 =
                            let uu____27691 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____27691)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____27676  in
                        FStar_Syntax_Syntax.mk uu____27675  in
                      uu____27668 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____27665))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____27728 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____27728 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____27787 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____27787
                       (fun uc  ->
                          let uu____27795 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____27795)
                 | (x,imp)::bs3 ->
                     let uu____27821 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____27821
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____27830 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27850) ->
          let uu____27855 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____27855
            (fun u_x  ->
               let uu____27863 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____27863)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____27868;
             FStar_Syntax_Syntax.vars = uu____27869;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____27948 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____27948 with
           | (unary_op1,uu____27968) ->
               let head1 =
                 let uu____27996 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____27996
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____28044;
             FStar_Syntax_Syntax.vars = uu____28045;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____28141 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____28141 with
           | (unary_op1,uu____28161) ->
               let head1 =
                 let uu____28189 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____28189
                  in
               let t2 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (head1, rest1))
                   FStar_Pervasives_Native.None t1.FStar_Syntax_Syntax.pos
                  in
               type_of_well_typed_term env t2)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____28245;
             FStar_Syntax_Syntax.vars = uu____28246;_},uu____28247::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____28286;
             FStar_Syntax_Syntax.vars = uu____28287;_},(t2,uu____28289)::uu____28290::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____28386 =
              let uu____28387 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____28387.FStar_Syntax_Syntax.n  in
            match uu____28386 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____28460 = FStar_Util.first_N n_args bs  in
                    match uu____28460 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____28548 =
                          let uu____28553 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____28553  in
                        (match uu____28548 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____28607 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____28607 with
                       | (bs1,c1) ->
                           let uu____28628 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____28628
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____28710  ->
                     match uu____28710 with
                     | (bs1,t2) ->
                         let subst1 =
                           FStar_List.map2
                             (fun b  ->
                                fun a  ->
                                  FStar_Syntax_Syntax.NT
                                    ((FStar_Pervasives_Native.fst b),
                                      (FStar_Pervasives_Native.fst a))) bs1
                             args
                            in
                         let uu____28786 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____28786)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____28788) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____28794,uu____28795) ->
                aux t2
            | uu____28836 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28837,(FStar_Util.Inl t2,uu____28839),uu____28840) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____28887,(FStar_Util.Inr c,uu____28889),uu____28890) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____28955 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____28955
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____28963) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____28968 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____28991 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____29005 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____29016 = type_of_well_typed_term env t  in
      match uu____29016 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____29022;
            FStar_Syntax_Syntax.vars = uu____29023;_}
          -> FStar_Pervasives_Native.Some u
      | uu____29026 -> FStar_Pervasives_Native.None

let (check_type_of_well_typed_term' :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___3873_29054 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3873_29054.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3873_29054.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3873_29054.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3873_29054.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3873_29054.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3873_29054.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3873_29054.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3873_29054.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3873_29054.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3873_29054.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3873_29054.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3873_29054.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3873_29054.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3873_29054.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3873_29054.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3873_29054.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3873_29054.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3873_29054.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3873_29054.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3873_29054.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3873_29054.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3873_29054.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3873_29054.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3873_29054.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3873_29054.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3873_29054.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3873_29054.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3873_29054.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3873_29054.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3873_29054.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3873_29054.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3873_29054.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3873_29054.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3873_29054.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3873_29054.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3873_29054.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3873_29054.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3873_29054.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3873_29054.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3873_29054.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3873_29054.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3873_29054.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3873_29054.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let slow_check uu____29061 =
            if must_total
            then
              let uu____29063 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____29063 with | (uu____29070,uu____29071,g) -> g
            else
              (let uu____29075 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____29075 with | (uu____29082,uu____29083,g) -> g)
             in
          let uu____29085 = type_of_well_typed_term env2 t  in
          match uu____29085 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____29090 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____29090
                then
                  let uu____29095 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____29097 = FStar_Syntax_Print.term_to_string t  in
                  let uu____29099 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____29101 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____29095 uu____29097 uu____29099 uu____29101
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____29110 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____29110
                 then
                   let uu____29115 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____29117 = FStar_Syntax_Print.term_to_string t  in
                   let uu____29119 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____29121 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____29115
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____29117 uu____29119 uu____29121
                 else ());
                (match g with
                 | FStar_Pervasives_Native.None  -> slow_check ()
                 | FStar_Pervasives_Native.Some g1 -> g1)))
  
let (check_type_of_well_typed_term :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.typ -> FStar_TypeChecker_Common.guard_t)
  =
  fun must_total  ->
    fun env  ->
      fun t  ->
        fun k  ->
          let env1 = FStar_TypeChecker_Env.set_expected_typ env k  in
          let env2 =
            let uu___3904_29158 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3904_29158.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3904_29158.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3904_29158.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3904_29158.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3904_29158.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3904_29158.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3904_29158.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3904_29158.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3904_29158.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3904_29158.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3904_29158.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3904_29158.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3904_29158.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3904_29158.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3904_29158.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3904_29158.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3904_29158.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3904_29158.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3904_29158.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3904_29158.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3904_29158.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3904_29158.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3904_29158.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3904_29158.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3904_29158.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3904_29158.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3904_29158.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3904_29158.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3904_29158.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3904_29158.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3904_29158.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3904_29158.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3904_29158.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3904_29158.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3904_29158.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3904_29158.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3904_29158.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3904_29158.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3904_29158.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3904_29158.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3904_29158.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3904_29158.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3904_29158.FStar_TypeChecker_Env.strict_args_tab)
            }  in
          let slow_check uu____29165 =
            if must_total
            then
              let uu____29167 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____29167 with | (uu____29174,uu____29175,g) -> g
            else
              (let uu____29179 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____29179 with | (uu____29186,uu____29187,g) -> g)
             in
          let uu____29189 =
            let uu____29191 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____29191  in
          if uu____29189
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  