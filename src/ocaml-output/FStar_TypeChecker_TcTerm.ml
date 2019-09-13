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
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___8_5.FStar_TypeChecker_Env.try_solve_implicits_hook);
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
        (uu___8_5.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___8_5.FStar_TypeChecker_Env.erasable_types_tab)
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
      FStar_TypeChecker_Env.try_solve_implicits_hook =
        (uu___11_13.FStar_TypeChecker_Env.try_solve_implicits_hook);
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
        (uu___11_13.FStar_TypeChecker_Env.strict_args_tab);
      FStar_TypeChecker_Env.erasable_types_tab =
        (uu___11_13.FStar_TypeChecker_Env.erasable_types_tab)
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
                FStar_TypeChecker_Env.try_solve_implicits_hook =
                  (uu___369_2322.FStar_TypeChecker_Env.try_solve_implicits_hook);
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
                  (uu___369_2322.FStar_TypeChecker_Env.strict_args_tab);
                FStar_TypeChecker_Env.erasable_types_tab =
                  (uu___369_2322.FStar_TypeChecker_Env.erasable_types_tab)
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
      (let uu____3571 = FStar_TypeChecker_Env.debug env FStar_Options.Medium
          in
       if uu____3571
       then
         let uu____3574 =
           let uu____3576 = FStar_TypeChecker_Env.get_range env  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3576  in
         let uu____3578 = FStar_Syntax_Print.term_to_string e  in
         let uu____3580 =
           let uu____3582 = FStar_Syntax_Subst.compress e  in
           FStar_Syntax_Print.tag_of_term uu____3582  in
         let uu____3583 =
           let uu____3585 = FStar_TypeChecker_Env.expected_typ env  in
           match uu____3585 with
           | FStar_Pervasives_Native.None  -> "None"
           | FStar_Pervasives_Native.Some t ->
               FStar_Syntax_Print.term_to_string t
            in
         FStar_Util.print4
           "(%s) Starting tc_term of %s (%s) with expected type: %s {\n"
           uu____3574 uu____3578 uu____3580 uu____3583
       else ());
      (let uu____3594 =
         FStar_Util.record_time
           (fun uu____3613  ->
              tc_maybe_toplevel_term
                (let uu___458_3616 = env  in
                 {
                   FStar_TypeChecker_Env.solver =
                     (uu___458_3616.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (uu___458_3616.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (uu___458_3616.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (uu___458_3616.FStar_TypeChecker_Env.gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (uu___458_3616.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (uu___458_3616.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (uu___458_3616.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (uu___458_3616.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (uu___458_3616.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (uu___458_3616.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.is_pattern =
                     (uu___458_3616.FStar_TypeChecker_Env.is_pattern);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (uu___458_3616.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (uu___458_3616.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (uu___458_3616.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (uu___458_3616.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level = false;
                   FStar_TypeChecker_Env.check_uvars =
                     (uu___458_3616.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq =
                     (uu___458_3616.FStar_TypeChecker_Env.use_eq);
                   FStar_TypeChecker_Env.is_iface =
                     (uu___458_3616.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (uu___458_3616.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (uu___458_3616.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (uu___458_3616.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (uu___458_3616.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (uu___458_3616.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (uu___458_3616.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (uu___458_3616.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.tc_term =
                     (uu___458_3616.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.type_of =
                     (uu___458_3616.FStar_TypeChecker_Env.type_of);
                   FStar_TypeChecker_Env.universe_of =
                     (uu___458_3616.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.check_type_of =
                     (uu___458_3616.FStar_TypeChecker_Env.check_type_of);
                   FStar_TypeChecker_Env.use_bv_sorts =
                     (uu___458_3616.FStar_TypeChecker_Env.use_bv_sorts);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (uu___458_3616.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (uu___458_3616.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (uu___458_3616.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (uu___458_3616.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (uu___458_3616.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (uu___458_3616.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (uu___458_3616.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.postprocess =
                     (uu___458_3616.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.is_native_tactic =
                     (uu___458_3616.FStar_TypeChecker_Env.is_native_tactic);
                   FStar_TypeChecker_Env.identifier_info =
                     (uu___458_3616.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (uu___458_3616.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (uu___458_3616.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (uu___458_3616.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (uu___458_3616.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (uu___458_3616.FStar_TypeChecker_Env.erasable_types_tab)
                 }) e)
          in
       match uu____3594 with
       | (r,ms) ->
           ((let uu____3641 =
               FStar_TypeChecker_Env.debug env FStar_Options.Medium  in
             if uu____3641
             then
               ((let uu____3645 =
                   let uu____3647 = FStar_TypeChecker_Env.get_range env  in
                   FStar_All.pipe_left FStar_Range.string_of_range uu____3647
                    in
                 let uu____3649 = FStar_Syntax_Print.term_to_string e  in
                 let uu____3651 =
                   let uu____3653 = FStar_Syntax_Subst.compress e  in
                   FStar_Syntax_Print.tag_of_term uu____3653  in
                 let uu____3654 = FStar_Util.string_of_int ms  in
                 FStar_Util.print4 "(%s) } tc_term of %s (%s) took %sms\n"
                   uu____3645 uu____3649 uu____3651 uu____3654);
                (let uu____3657 = r  in
                 match uu____3657 with
                 | (e1,lc,uu____3666) ->
                     let uu____3667 =
                       let uu____3669 = FStar_TypeChecker_Env.get_range env
                          in
                       FStar_All.pipe_left FStar_Range.string_of_range
                         uu____3669
                        in
                     let uu____3671 = FStar_Syntax_Print.term_to_string e1
                        in
                     let uu____3673 =
                       FStar_TypeChecker_Common.lcomp_to_string lc  in
                     let uu____3675 =
                       let uu____3677 = FStar_Syntax_Subst.compress e1  in
                       FStar_Syntax_Print.tag_of_term uu____3677  in
                     FStar_Util.print4 "(%s) Result is: (%s:%s) (%s)\n"
                       uu____3667 uu____3671 uu____3673 uu____3675))
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
      (let uu____3695 = FStar_TypeChecker_Env.debug env1 FStar_Options.Medium
          in
       if uu____3695
       then
         let uu____3698 =
           let uu____3700 = FStar_TypeChecker_Env.get_range env1  in
           FStar_All.pipe_left FStar_Range.string_of_range uu____3700  in
         let uu____3702 = FStar_Syntax_Print.tag_of_term top  in
         let uu____3704 = FStar_Syntax_Print.term_to_string top  in
         FStar_Util.print3 "Typechecking %s (%s): %s\n" uu____3698 uu____3702
           uu____3704
       else ());
      (match top.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3715 -> failwith "Impossible"
       | FStar_Syntax_Syntax.Tm_uinst uu____3745 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_uvar uu____3752 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_bvar uu____3765 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_name uu____3766 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_fvar uu____3767 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_constant uu____3768 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_abs uu____3769 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_arrow uu____3788 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_refine uu____3803 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_type uu____3810 -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_unknown  -> tc_value env1 e
       | FStar_Syntax_Syntax.Tm_quoted (qt,qi) ->
           let projl uu___2_3826 =
             match uu___2_3826 with
             | FStar_Util.Inl x -> x
             | FStar_Util.Inr uu____3832 -> failwith "projl fail"  in
           let non_trivial_antiquotes qi1 =
             let is_name1 t =
               let uu____3848 =
                 let uu____3849 = FStar_Syntax_Subst.compress t  in
                 uu____3849.FStar_Syntax_Syntax.n  in
               match uu____3848 with
               | FStar_Syntax_Syntax.Tm_name uu____3853 -> true
               | uu____3855 -> false  in
             FStar_Util.for_some
               (fun uu____3865  ->
                  match uu____3865 with
                  | (uu____3871,t) ->
                      let uu____3873 = is_name1 t  in
                      Prims.op_Negation uu____3873)
               qi1.FStar_Syntax_Syntax.antiquotes
              in
           (match qi.FStar_Syntax_Syntax.qkind with
            | FStar_Syntax_Syntax.Quote_static  when
                non_trivial_antiquotes qi ->
                let e0 = e  in
                let newbvs =
                  FStar_List.map
                    (fun uu____3892  ->
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None
                         FStar_Syntax_Syntax.t_term)
                    qi.FStar_Syntax_Syntax.antiquotes
                   in
                let z =
                  FStar_List.zip qi.FStar_Syntax_Syntax.antiquotes newbvs  in
                let lbs =
                  FStar_List.map
                    (fun uu____3935  ->
                       match uu____3935 with
                       | ((bv,t),bv') ->
                           FStar_Syntax_Util.close_univs_and_mk_letbinding
                             FStar_Pervasives_Native.None
                             (FStar_Util.Inl bv') []
                             FStar_Syntax_Syntax.t_term
                             FStar_Parser_Const.effect_Tot_lid t []
                             t.FStar_Syntax_Syntax.pos) z
                   in
                let qi1 =
                  let uu___531_3964 = qi  in
                  let uu____3965 =
                    FStar_List.map
                      (fun uu____3993  ->
                         match uu____3993 with
                         | ((bv,uu____4009),bv') ->
                             let uu____4021 =
                               FStar_Syntax_Syntax.bv_to_name bv'  in
                             (bv, uu____4021)) z
                     in
                  {
                    FStar_Syntax_Syntax.qkind =
                      (uu___531_3964.FStar_Syntax_Syntax.qkind);
                    FStar_Syntax_Syntax.antiquotes = uu____3965
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
                         let uu____4033 =
                           let uu____4040 =
                             let uu____4041 =
                               let uu____4055 =
                                 let uu____4058 =
                                   let uu____4059 =
                                     let uu____4066 =
                                       projl lb.FStar_Syntax_Syntax.lbname
                                        in
                                     FStar_Syntax_Syntax.mk_binder uu____4066
                                      in
                                   [uu____4059]  in
                                 FStar_Syntax_Subst.close uu____4058 t  in
                               ((false, [lb]), uu____4055)  in
                             FStar_Syntax_Syntax.Tm_let uu____4041  in
                           FStar_Syntax_Syntax.mk uu____4040  in
                         uu____4033 FStar_Pervasives_Native.None
                           top.FStar_Syntax_Syntax.pos) nq lbs
                   in
                tc_maybe_toplevel_term env1 e1
            | FStar_Syntax_Syntax.Quote_static  ->
                let aqs = qi.FStar_Syntax_Syntax.antiquotes  in
                let env_tm =
                  FStar_TypeChecker_Env.set_expected_typ env1
                    FStar_Syntax_Syntax.t_term
                   in
                let uu____4102 =
                  FStar_List.fold_right
                    (fun uu____4138  ->
                       fun uu____4139  ->
                         match (uu____4138, uu____4139) with
                         | ((bv,tm),(aqs_rev,guard)) ->
                             let uu____4208 = tc_term env_tm tm  in
                             (match uu____4208 with
                              | (tm1,uu____4226,g) ->
                                  let uu____4228 =
                                    FStar_TypeChecker_Env.conj_guard g guard
                                     in
                                  (((bv, tm1) :: aqs_rev), uu____4228))) aqs
                    ([], FStar_TypeChecker_Env.trivial_guard)
                   in
                (match uu____4102 with
                 | (aqs_rev,guard) ->
                     let qi1 =
                       let uu___559_4270 = qi  in
                       {
                         FStar_Syntax_Syntax.qkind =
                           (uu___559_4270.FStar_Syntax_Syntax.qkind);
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
                let uu____4289 =
                  FStar_TypeChecker_Env.clear_expected_typ env1  in
                (match uu____4289 with
                 | (env',uu____4303) ->
                     let uu____4308 =
                       tc_term
                         (let uu___568_4317 = env'  in
                          {
                            FStar_TypeChecker_Env.solver =
                              (uu___568_4317.FStar_TypeChecker_Env.solver);
                            FStar_TypeChecker_Env.range =
                              (uu___568_4317.FStar_TypeChecker_Env.range);
                            FStar_TypeChecker_Env.curmodule =
                              (uu___568_4317.FStar_TypeChecker_Env.curmodule);
                            FStar_TypeChecker_Env.gamma =
                              (uu___568_4317.FStar_TypeChecker_Env.gamma);
                            FStar_TypeChecker_Env.gamma_sig =
                              (uu___568_4317.FStar_TypeChecker_Env.gamma_sig);
                            FStar_TypeChecker_Env.gamma_cache =
                              (uu___568_4317.FStar_TypeChecker_Env.gamma_cache);
                            FStar_TypeChecker_Env.modules =
                              (uu___568_4317.FStar_TypeChecker_Env.modules);
                            FStar_TypeChecker_Env.expected_typ =
                              (uu___568_4317.FStar_TypeChecker_Env.expected_typ);
                            FStar_TypeChecker_Env.sigtab =
                              (uu___568_4317.FStar_TypeChecker_Env.sigtab);
                            FStar_TypeChecker_Env.attrtab =
                              (uu___568_4317.FStar_TypeChecker_Env.attrtab);
                            FStar_TypeChecker_Env.is_pattern =
                              (uu___568_4317.FStar_TypeChecker_Env.is_pattern);
                            FStar_TypeChecker_Env.instantiate_imp =
                              (uu___568_4317.FStar_TypeChecker_Env.instantiate_imp);
                            FStar_TypeChecker_Env.effects =
                              (uu___568_4317.FStar_TypeChecker_Env.effects);
                            FStar_TypeChecker_Env.generalize =
                              (uu___568_4317.FStar_TypeChecker_Env.generalize);
                            FStar_TypeChecker_Env.letrecs =
                              (uu___568_4317.FStar_TypeChecker_Env.letrecs);
                            FStar_TypeChecker_Env.top_level =
                              (uu___568_4317.FStar_TypeChecker_Env.top_level);
                            FStar_TypeChecker_Env.check_uvars =
                              (uu___568_4317.FStar_TypeChecker_Env.check_uvars);
                            FStar_TypeChecker_Env.use_eq =
                              (uu___568_4317.FStar_TypeChecker_Env.use_eq);
                            FStar_TypeChecker_Env.is_iface =
                              (uu___568_4317.FStar_TypeChecker_Env.is_iface);
                            FStar_TypeChecker_Env.admit =
                              (uu___568_4317.FStar_TypeChecker_Env.admit);
                            FStar_TypeChecker_Env.lax = true;
                            FStar_TypeChecker_Env.lax_universes =
                              (uu___568_4317.FStar_TypeChecker_Env.lax_universes);
                            FStar_TypeChecker_Env.phase1 =
                              (uu___568_4317.FStar_TypeChecker_Env.phase1);
                            FStar_TypeChecker_Env.failhard =
                              (uu___568_4317.FStar_TypeChecker_Env.failhard);
                            FStar_TypeChecker_Env.nosynth =
                              (uu___568_4317.FStar_TypeChecker_Env.nosynth);
                            FStar_TypeChecker_Env.uvar_subtyping =
                              (uu___568_4317.FStar_TypeChecker_Env.uvar_subtyping);
                            FStar_TypeChecker_Env.tc_term =
                              (uu___568_4317.FStar_TypeChecker_Env.tc_term);
                            FStar_TypeChecker_Env.type_of =
                              (uu___568_4317.FStar_TypeChecker_Env.type_of);
                            FStar_TypeChecker_Env.universe_of =
                              (uu___568_4317.FStar_TypeChecker_Env.universe_of);
                            FStar_TypeChecker_Env.check_type_of =
                              (uu___568_4317.FStar_TypeChecker_Env.check_type_of);
                            FStar_TypeChecker_Env.use_bv_sorts =
                              (uu___568_4317.FStar_TypeChecker_Env.use_bv_sorts);
                            FStar_TypeChecker_Env.qtbl_name_and_index =
                              (uu___568_4317.FStar_TypeChecker_Env.qtbl_name_and_index);
                            FStar_TypeChecker_Env.normalized_eff_names =
                              (uu___568_4317.FStar_TypeChecker_Env.normalized_eff_names);
                            FStar_TypeChecker_Env.fv_delta_depths =
                              (uu___568_4317.FStar_TypeChecker_Env.fv_delta_depths);
                            FStar_TypeChecker_Env.proof_ns =
                              (uu___568_4317.FStar_TypeChecker_Env.proof_ns);
                            FStar_TypeChecker_Env.synth_hook =
                              (uu___568_4317.FStar_TypeChecker_Env.synth_hook);
                            FStar_TypeChecker_Env.try_solve_implicits_hook =
                              (uu___568_4317.FStar_TypeChecker_Env.try_solve_implicits_hook);
                            FStar_TypeChecker_Env.splice =
                              (uu___568_4317.FStar_TypeChecker_Env.splice);
                            FStar_TypeChecker_Env.postprocess =
                              (uu___568_4317.FStar_TypeChecker_Env.postprocess);
                            FStar_TypeChecker_Env.is_native_tactic =
                              (uu___568_4317.FStar_TypeChecker_Env.is_native_tactic);
                            FStar_TypeChecker_Env.identifier_info =
                              (uu___568_4317.FStar_TypeChecker_Env.identifier_info);
                            FStar_TypeChecker_Env.tc_hooks =
                              (uu___568_4317.FStar_TypeChecker_Env.tc_hooks);
                            FStar_TypeChecker_Env.dsenv =
                              (uu___568_4317.FStar_TypeChecker_Env.dsenv);
                            FStar_TypeChecker_Env.nbe =
                              (uu___568_4317.FStar_TypeChecker_Env.nbe);
                            FStar_TypeChecker_Env.strict_args_tab =
                              (uu___568_4317.FStar_TypeChecker_Env.strict_args_tab);
                            FStar_TypeChecker_Env.erasable_types_tab =
                              (uu___568_4317.FStar_TypeChecker_Env.erasable_types_tab)
                          }) qt
                        in
                     (match uu____4308 with
                      | (qt1,uu____4326,uu____4327) ->
                          let t =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_quoted (qt1, qi))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4333 =
                            let uu____4340 =
                              let uu____4345 =
                                FStar_TypeChecker_Common.lcomp_of_comp c  in
                              FStar_Util.Inr uu____4345  in
                            value_check_expected_typ env1 top uu____4340
                              FStar_TypeChecker_Env.trivial_guard
                             in
                          (match uu____4333 with
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
           { FStar_Syntax_Syntax.blob = uu____4362;
             FStar_Syntax_Syntax.lkind = FStar_Syntax_Syntax.Lazy_embedding
               uu____4363;
             FStar_Syntax_Syntax.ltyp = uu____4364;
             FStar_Syntax_Syntax.rng = uu____4365;_}
           ->
           let uu____4376 = FStar_Syntax_Util.unlazy top  in
           tc_term env1 uu____4376
       | FStar_Syntax_Syntax.Tm_lazy i ->
           value_check_expected_typ env1 top
             (FStar_Util.Inl (i.FStar_Syntax_Syntax.ltyp))
             FStar_TypeChecker_Env.trivial_guard
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Meta_smt_pat ))
           ->
           let uu____4383 = tc_tot_or_gtot_term env1 e1  in
           (match uu____4383 with
            | (e2,c,g) ->
                let g1 =
                  let uu___598_4400 = g  in
                  {
                    FStar_TypeChecker_Common.guard_f =
                      FStar_TypeChecker_Common.Trivial;
                    FStar_TypeChecker_Common.deferred =
                      (uu___598_4400.FStar_TypeChecker_Common.deferred);
                    FStar_TypeChecker_Common.univ_ineqs =
                      (uu___598_4400.FStar_TypeChecker_Common.univ_ineqs);
                    FStar_TypeChecker_Common.implicits =
                      (uu___598_4400.FStar_TypeChecker_Common.implicits)
                  }  in
                let uu____4401 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta
                       (e2,
                         (FStar_Syntax_Syntax.Meta_desugared
                            FStar_Syntax_Syntax.Meta_smt_pat)))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (uu____4401, c, g1))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_pattern (names1,pats)) ->
           let uu____4443 = FStar_Syntax_Util.type_u ()  in
           (match uu____4443 with
            | (t,u) ->
                let uu____4456 = tc_check_tot_or_gtot_term env1 e1 t  in
                (match uu____4456 with
                 | (e2,c,g) ->
                     let uu____4472 =
                       let uu____4489 =
                         FStar_TypeChecker_Env.clear_expected_typ env1  in
                       match uu____4489 with
                       | (env2,uu____4513) -> tc_smt_pats env2 pats  in
                     (match uu____4472 with
                      | (pats1,g') ->
                          let g'1 =
                            let uu___621_4551 = g'  in
                            {
                              FStar_TypeChecker_Common.guard_f =
                                FStar_TypeChecker_Common.Trivial;
                              FStar_TypeChecker_Common.deferred =
                                (uu___621_4551.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (uu___621_4551.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (uu___621_4551.FStar_TypeChecker_Common.implicits)
                            }  in
                          let uu____4552 =
                            FStar_Syntax_Syntax.mk
                              (FStar_Syntax_Syntax.Tm_meta
                                 (e2,
                                   (FStar_Syntax_Syntax.Meta_pattern
                                      (names1, pats1))))
                              FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          let uu____4571 =
                            FStar_TypeChecker_Env.conj_guard g g'1  in
                          (uu____4552, c, uu____4571))))
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_desugared
            (FStar_Syntax_Syntax.Sequence ))
           ->
           let uu____4577 =
             let uu____4578 = FStar_Syntax_Subst.compress e1  in
             uu____4578.FStar_Syntax_Syntax.n  in
           (match uu____4577 with
            | FStar_Syntax_Syntax.Tm_let
                ((uu____4587,{ FStar_Syntax_Syntax.lbname = x;
                               FStar_Syntax_Syntax.lbunivs = uu____4589;
                               FStar_Syntax_Syntax.lbtyp = uu____4590;
                               FStar_Syntax_Syntax.lbeff = uu____4591;
                               FStar_Syntax_Syntax.lbdef = e11;
                               FStar_Syntax_Syntax.lbattrs = uu____4593;
                               FStar_Syntax_Syntax.lbpos = uu____4594;_}::[]),e2)
                ->
                let uu____4625 =
                  let uu____4632 =
                    FStar_TypeChecker_Env.set_expected_typ env1
                      FStar_Syntax_Syntax.t_unit
                     in
                  tc_term uu____4632 e11  in
                (match uu____4625 with
                 | (e12,c1,g1) ->
                     let uu____4642 = tc_term env1 e2  in
                     (match uu____4642 with
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
                            let uu____4666 =
                              FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                env1 c1.FStar_TypeChecker_Common.eff_name
                               in
                            if uu____4666
                            then [FStar_Syntax_Util.inline_let_attr]
                            else []  in
                          let e3 =
                            let uu____4676 =
                              let uu____4683 =
                                let uu____4684 =
                                  let uu____4698 =
                                    let uu____4706 =
                                      let uu____4709 =
                                        FStar_Syntax_Syntax.mk_lb
                                          (x, [],
                                            (c1.FStar_TypeChecker_Common.eff_name),
                                            FStar_Syntax_Syntax.t_unit, e13,
                                            attrs,
                                            (e13.FStar_Syntax_Syntax.pos))
                                         in
                                      [uu____4709]  in
                                    (false, uu____4706)  in
                                  (uu____4698, e22)  in
                                FStar_Syntax_Syntax.Tm_let uu____4684  in
                              FStar_Syntax_Syntax.mk uu____4683  in
                            uu____4676 FStar_Pervasives_Native.None
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
                          let uu____4733 =
                            FStar_TypeChecker_Env.conj_guard g1 g2  in
                          (e5, c, uu____4733)))
            | uu____4734 ->
                let uu____4735 = tc_term env1 e1  in
                (match uu____4735 with
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
           (e1,FStar_Syntax_Syntax.Meta_monadic uu____4757) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta
           (e1,FStar_Syntax_Syntax.Meta_monadic_lift uu____4769) ->
           tc_term env1 e1
       | FStar_Syntax_Syntax.Tm_meta (e1,m) ->
           let uu____4788 = tc_term env1 e1  in
           (match uu____4788 with
            | (e2,c,g) ->
                let e3 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_meta (e2, m))
                    FStar_Pervasives_Native.None top.FStar_Syntax_Syntax.pos
                   in
                (e3, c, g))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inr expected_c,topt),uu____4812) ->
           let uu____4859 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____4859 with
            | (env0,uu____4873) ->
                let uu____4878 = tc_comp env0 expected_c  in
                (match uu____4878 with
                 | (expected_c1,uu____4892,g) ->
                     let uu____4894 =
                       let uu____4901 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.comp_result expected_c1)
                           (FStar_TypeChecker_Env.set_expected_typ env0)
                          in
                       tc_term uu____4901 e1  in
                     (match uu____4894 with
                      | (e2,c',g') ->
                          let uu____4911 =
                            let uu____4922 =
                              FStar_TypeChecker_Common.lcomp_comp c'  in
                            match uu____4922 with
                            | (c'1,g_c') ->
                                let uu____4939 =
                                  check_expected_effect env0
                                    (FStar_Pervasives_Native.Some expected_c1)
                                    (e2, c'1)
                                   in
                                (match uu____4939 with
                                 | (e3,expected_c2,g'') ->
                                     let uu____4959 =
                                       FStar_TypeChecker_Env.conj_guard g_c'
                                         g''
                                        in
                                     (e3, expected_c2, uu____4959))
                             in
                          (match uu____4911 with
                           | (e3,expected_c2,g'') ->
                               let uu____4981 = tc_tactic_opt env0 topt  in
                               (match uu____4981 with
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
                                      let uu____5041 =
                                        FStar_TypeChecker_Env.conj_guard g'
                                          g''
                                         in
                                      FStar_TypeChecker_Env.conj_guard g
                                        uu____5041
                                       in
                                    let uu____5042 =
                                      comp_check_expected_typ env1 e4 lc  in
                                    (match uu____5042 with
                                     | (e5,c,f2) ->
                                         let final_guard =
                                           let uu____5059 =
                                             FStar_TypeChecker_Env.conj_guard
                                               f f2
                                              in
                                           wrap_guard_with_tactic_opt topt1
                                             uu____5059
                                            in
                                         let uu____5060 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard gtac
                                            in
                                         (e5, c, uu____5060)))))))
       | FStar_Syntax_Syntax.Tm_ascribed
           (e1,(FStar_Util.Inl t,topt),uu____5064) ->
           let uu____5111 = FStar_Syntax_Util.type_u ()  in
           (match uu____5111 with
            | (k,u) ->
                let uu____5124 = tc_check_tot_or_gtot_term env1 t k  in
                (match uu____5124 with
                 | (t1,uu____5138,f) ->
                     let uu____5140 = tc_tactic_opt env1 topt  in
                     (match uu____5140 with
                      | (topt1,gtac) ->
                          let uu____5159 =
                            let uu____5166 =
                              FStar_TypeChecker_Env.set_expected_typ env1 t1
                               in
                            tc_term uu____5166 e1  in
                          (match uu____5159 with
                           | (e2,c,g) ->
                               let uu____5176 =
                                 let uu____5181 =
                                   FStar_TypeChecker_Env.set_range env1
                                     t1.FStar_Syntax_Syntax.pos
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   (FStar_Pervasives_Native.Some
                                      (fun uu____5187  ->
                                         FStar_Util.return_all
                                           FStar_TypeChecker_Err.ill_kinded_type))
                                   uu____5181 e2 c f
                                  in
                               (match uu____5176 with
                                | (c1,f1) ->
                                    let uu____5197 =
                                      let uu____5204 =
                                        FStar_Syntax_Syntax.mk
                                          (FStar_Syntax_Syntax.Tm_ascribed
                                             (e2,
                                               ((FStar_Util.Inl t1), topt1),
                                               (FStar_Pervasives_Native.Some
                                                  (c1.FStar_TypeChecker_Common.eff_name))))
                                          FStar_Pervasives_Native.None
                                          top.FStar_Syntax_Syntax.pos
                                         in
                                      comp_check_expected_typ env1 uu____5204
                                        c1
                                       in
                                    (match uu____5197 with
                                     | (e3,c2,f2) ->
                                         let final_guard =
                                           let uu____5251 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g f2
                                              in
                                           FStar_TypeChecker_Env.conj_guard
                                             f1 uu____5251
                                            in
                                         let final_guard1 =
                                           wrap_guard_with_tactic_opt topt1
                                             final_guard
                                            in
                                         let uu____5253 =
                                           FStar_TypeChecker_Env.conj_guard
                                             final_guard1 gtac
                                            in
                                         (e3, c2, uu____5253)))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____5254;
              FStar_Syntax_Syntax.vars = uu____5255;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5334 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5334 with
            | (unary_op1,uu____5358) ->
                let head1 =
                  let uu____5386 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5386
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
              FStar_Syntax_Syntax.pos = uu____5434;
              FStar_Syntax_Syntax.vars = uu____5435;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5514 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5514 with
            | (unary_op1,uu____5538) ->
                let head1 =
                  let uu____5566 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5566
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
                (FStar_Const.Const_reflect uu____5614);
              FStar_Syntax_Syntax.pos = uu____5615;
              FStar_Syntax_Syntax.vars = uu____5616;_},a::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5695 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5695 with
            | (unary_op1,uu____5719) ->
                let head1 =
                  let uu____5747 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                    FStar_Pervasives_Native.None uu____5747
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
              FStar_Syntax_Syntax.pos = uu____5795;
              FStar_Syntax_Syntax.vars = uu____5796;_},a1::a2::hd1::rest)
           ->
           let rest1 = hd1 :: rest  in
           let uu____5892 = FStar_Syntax_Util.head_and_args top  in
           (match uu____5892 with
            | (unary_op1,uu____5916) ->
                let head1 =
                  let uu____5944 =
                    FStar_Range.union_ranges
                      unary_op1.FStar_Syntax_Syntax.pos
                      (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                     in
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                    FStar_Pervasives_Native.None uu____5944
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
              FStar_Syntax_Syntax.pos = uu____6000;
              FStar_Syntax_Syntax.vars = uu____6001;_},(e1,FStar_Pervasives_Native.None
                                                        )::[])
           ->
           let uu____6039 =
             let uu____6046 =
               let uu____6047 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_left FStar_Pervasives_Native.fst uu____6047  in
             tc_term uu____6046 e1  in
           (match uu____6039 with
            | (e2,c,g) ->
                let uu____6071 = FStar_Syntax_Util.head_and_args top  in
                (match uu____6071 with
                 | (head1,uu____6095) ->
                     let uu____6120 =
                       FStar_Syntax_Syntax.mk
                         (FStar_Syntax_Syntax.Tm_app
                            (head1, [(e2, FStar_Pervasives_Native.None)]))
                         FStar_Pervasives_Native.None
                         top.FStar_Syntax_Syntax.pos
                        in
                     let uu____6153 =
                       let uu____6154 =
                         let uu____6155 =
                           FStar_Syntax_Syntax.tabbrev
                             FStar_Parser_Const.range_lid
                            in
                         FStar_Syntax_Syntax.mk_Total uu____6155  in
                       FStar_All.pipe_left
                         FStar_TypeChecker_Common.lcomp_of_comp uu____6154
                        in
                     (uu____6120, uu____6153, g)))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6156;
              FStar_Syntax_Syntax.vars = uu____6157;_},(t,FStar_Pervasives_Native.None
                                                        )::(r,FStar_Pervasives_Native.None
                                                            )::[])
           ->
           let uu____6210 = FStar_Syntax_Util.head_and_args top  in
           (match uu____6210 with
            | (head1,uu____6234) ->
                let env' =
                  let uu____6260 =
                    FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid
                     in
                  FStar_TypeChecker_Env.set_expected_typ env1 uu____6260  in
                let uu____6261 = tc_term env' r  in
                (match uu____6261 with
                 | (er,uu____6275,gr) ->
                     let uu____6277 = tc_term env1 t  in
                     (match uu____6277 with
                      | (t1,tt,gt1) ->
                          let g = FStar_TypeChecker_Env.conj_guard gr gt1  in
                          let uu____6294 =
                            let uu____6295 =
                              let uu____6300 =
                                let uu____6301 =
                                  FStar_Syntax_Syntax.as_arg t1  in
                                let uu____6310 =
                                  let uu____6321 =
                                    FStar_Syntax_Syntax.as_arg r  in
                                  [uu____6321]  in
                                uu____6301 :: uu____6310  in
                              FStar_Syntax_Syntax.mk_Tm_app head1 uu____6300
                               in
                            uu____6295 FStar_Pervasives_Native.None
                              top.FStar_Syntax_Syntax.pos
                             in
                          (uu____6294, tt, g))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_range_of );
              FStar_Syntax_Syntax.pos = uu____6354;
              FStar_Syntax_Syntax.vars = uu____6355;_},uu____6356)
           ->
           let uu____6381 =
             let uu____6387 =
               let uu____6389 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6389  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6387)  in
           FStar_Errors.raise_error uu____6381 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_set_range_of );
              FStar_Syntax_Syntax.pos = uu____6399;
              FStar_Syntax_Syntax.vars = uu____6400;_},uu____6401)
           ->
           let uu____6426 =
             let uu____6432 =
               let uu____6434 = FStar_Syntax_Print.term_to_string top  in
               FStar_Util.format1 "Ill-applied constant %s" uu____6434  in
             (FStar_Errors.Fatal_IllAppliedConstant, uu____6432)  in
           FStar_Errors.raise_error uu____6426 e.FStar_Syntax_Syntax.pos
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reify );
              FStar_Syntax_Syntax.pos = uu____6444;
              FStar_Syntax_Syntax.vars = uu____6445;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReify,
                  "Qualifier on argument to reify is irrelevant and will be ignored")
            else ();
            (let uu____6492 = FStar_TypeChecker_Env.clear_expected_typ env1
                in
             match uu____6492 with
             | (env0,uu____6506) ->
                 let uu____6511 = tc_term env0 e1  in
                 (match uu____6511 with
                  | (e2,c,g) ->
                      let uu____6527 = FStar_Syntax_Util.head_and_args top
                         in
                      (match uu____6527 with
                       | (reify_op,uu____6551) ->
                           let u_c =
                             env1.FStar_TypeChecker_Env.universe_of env1
                               c.FStar_TypeChecker_Common.res_typ
                              in
                           let uu____6577 =
                             FStar_TypeChecker_Common.lcomp_comp c  in
                           (match uu____6577 with
                            | (c1,g_c) ->
                                let ef =
                                  FStar_Syntax_Util.comp_effect_name c1  in
                                ((let uu____6592 =
                                    let uu____6594 =
                                      FStar_TypeChecker_Env.is_user_reifiable_effect
                                        env1 ef
                                       in
                                    Prims.op_Negation uu____6594  in
                                  if uu____6592
                                  then
                                    let uu____6597 =
                                      let uu____6603 =
                                        FStar_Util.format1
                                          "Effect %s cannot be reified"
                                          ef.FStar_Ident.str
                                         in
                                      (FStar_Errors.Fatal_EffectCannotBeReified,
                                        uu____6603)
                                       in
                                    FStar_Errors.raise_error uu____6597
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
                                    let uu____6646 =
                                      FStar_TypeChecker_Env.is_total_effect
                                        env1 ef
                                       in
                                    if uu____6646
                                    then
                                      let uu____6649 =
                                        FStar_Syntax_Syntax.mk_Total repr  in
                                      FStar_All.pipe_right uu____6649
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
                                       let uu____6661 =
                                         FStar_Syntax_Syntax.mk_Comp ct  in
                                       FStar_All.pipe_right uu____6661
                                         FStar_TypeChecker_Common.lcomp_of_comp)
                                     in
                                  let uu____6662 =
                                    comp_check_expected_typ env1 e3 c2  in
                                  match uu____6662 with
                                  | (e4,c3,g') ->
                                      let uu____6678 =
                                        let uu____6679 =
                                          FStar_TypeChecker_Env.conj_guard
                                            g_c g'
                                           in
                                        FStar_TypeChecker_Env.conj_guard g
                                          uu____6679
                                         in
                                      (e4, c3, uu____6678))))))))
       | FStar_Syntax_Syntax.Tm_app
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_reflect l);
              FStar_Syntax_Syntax.pos = uu____6681;
              FStar_Syntax_Syntax.vars = uu____6682;_},(e1,aqual)::[])
           ->
           (if FStar_Option.isSome aqual
            then
              FStar_Errors.log_issue e1.FStar_Syntax_Syntax.pos
                (FStar_Errors.Warning_IrrelevantQualifierOnArgumentToReflect,
                  "Qualifier on argument to reflect is irrelevant and will be ignored")
            else ();
            (let uu____6730 =
               let uu____6732 =
                 FStar_TypeChecker_Env.is_user_reifiable_effect env1 l  in
               Prims.op_Negation uu____6732  in
             if uu____6730
             then
               let uu____6735 =
                 let uu____6741 =
                   FStar_Util.format1 "Effect %s cannot be reified"
                     l.FStar_Ident.str
                    in
                 (FStar_Errors.Fatal_EffectCannotBeReified, uu____6741)  in
               FStar_Errors.raise_error uu____6735 e1.FStar_Syntax_Syntax.pos
             else ());
            (let uu____6747 = FStar_Syntax_Util.head_and_args top  in
             match uu____6747 with
             | (reflect_op,uu____6771) ->
                 let uu____6796 =
                   FStar_TypeChecker_Env.effect_decl_opt env1 l  in
                 (match uu____6796 with
                  | FStar_Pervasives_Native.None  ->
                      failwith
                        "internal error: user reifiable effect has no decl?"
                  | FStar_Pervasives_Native.Some (ed,qualifiers) ->
                      let uu____6836 =
                        FStar_TypeChecker_Env.clear_expected_typ env1  in
                      (match uu____6836 with
                       | (env_no_ex,topt) ->
                           let uu____6855 =
                             let u = FStar_TypeChecker_Env.new_u_univ ()  in
                             let repr =
                               FStar_TypeChecker_Env.inst_effect_fun_with 
                                 [u] env1 ed ed.FStar_Syntax_Syntax.repr
                                in
                             let t =
                               let uu____6871 =
                                 let uu____6878 =
                                   let uu____6879 =
                                     let uu____6896 =
                                       let uu____6907 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.tun
                                          in
                                       let uu____6916 =
                                         let uu____6927 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.tun
                                            in
                                         [uu____6927]  in
                                       uu____6907 :: uu____6916  in
                                     (repr, uu____6896)  in
                                   FStar_Syntax_Syntax.Tm_app uu____6879  in
                                 FStar_Syntax_Syntax.mk uu____6878  in
                               uu____6871 FStar_Pervasives_Native.None
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____6972 =
                               let uu____6979 =
                                 let uu____6980 =
                                   FStar_TypeChecker_Env.clear_expected_typ
                                     env1
                                    in
                                 FStar_All.pipe_right uu____6980
                                   FStar_Pervasives_Native.fst
                                  in
                               tc_tot_or_gtot_term uu____6979 t  in
                             match uu____6972 with
                             | (t1,uu____7006,g) ->
                                 let uu____7008 =
                                   let uu____7009 =
                                     FStar_Syntax_Subst.compress t1  in
                                   uu____7009.FStar_Syntax_Syntax.n  in
                                 (match uu____7008 with
                                  | FStar_Syntax_Syntax.Tm_app
                                      (uu____7022,(res,uu____7024)::(wp,uu____7026)::[])
                                      -> (t1, res, wp, g)
                                  | uu____7083 -> failwith "Impossible")
                              in
                           (match uu____6855 with
                            | (expected_repr_typ,res_typ,wp,g0) ->
                                let uu____7109 =
                                  let uu____7116 =
                                    tc_tot_or_gtot_term env_no_ex e1  in
                                  match uu____7116 with
                                  | (e2,c,g) ->
                                      ((let uu____7133 =
                                          let uu____7135 =
                                            FStar_TypeChecker_Common.is_total_lcomp
                                              c
                                             in
                                          FStar_All.pipe_left
                                            Prims.op_Negation uu____7135
                                           in
                                        if uu____7133
                                        then
                                          FStar_TypeChecker_Err.add_errors
                                            env1
                                            [(FStar_Errors.Error_UnexpectedGTotComputation,
                                               "Expected Tot, got a GTot computation",
                                               (e2.FStar_Syntax_Syntax.pos))]
                                        else ());
                                       (let uu____7158 =
                                          FStar_TypeChecker_Rel.try_teq true
                                            env_no_ex
                                            c.FStar_TypeChecker_Common.res_typ
                                            expected_repr_typ
                                           in
                                        match uu____7158 with
                                        | FStar_Pervasives_Native.None  ->
                                            ((let uu____7169 =
                                                let uu____7179 =
                                                  let uu____7187 =
                                                    let uu____7189 =
                                                      FStar_Syntax_Print.tscheme_to_string
                                                        ed.FStar_Syntax_Syntax.repr
                                                       in
                                                    let uu____7191 =
                                                      FStar_Syntax_Print.term_to_string
                                                        c.FStar_TypeChecker_Common.res_typ
                                                       in
                                                    FStar_Util.format2
                                                      "Expected an instance of %s; got %s"
                                                      uu____7189 uu____7191
                                                     in
                                                  (FStar_Errors.Error_UnexpectedInstance,
                                                    uu____7187,
                                                    (e2.FStar_Syntax_Syntax.pos))
                                                   in
                                                [uu____7179]  in
                                              FStar_TypeChecker_Err.add_errors
                                                env1 uu____7169);
                                             (let uu____7209 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              (e2, uu____7209)))
                                        | FStar_Pervasives_Native.Some g' ->
                                            let uu____7213 =
                                              let uu____7214 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g0
                                                 in
                                              FStar_TypeChecker_Env.conj_guard
                                                g' uu____7214
                                               in
                                            (e2, uu____7213)))
                                   in
                                (match uu____7109 with
                                 | (e2,g) ->
                                     let c =
                                       let uu____7230 =
                                         let uu____7231 =
                                           let uu____7232 =
                                             let uu____7233 =
                                               env1.FStar_TypeChecker_Env.universe_of
                                                 env1 res_typ
                                                in
                                             [uu____7233]  in
                                           let uu____7234 =
                                             let uu____7245 =
                                               FStar_Syntax_Syntax.as_arg wp
                                                in
                                             [uu____7245]  in
                                           {
                                             FStar_Syntax_Syntax.comp_univs =
                                               uu____7232;
                                             FStar_Syntax_Syntax.effect_name
                                               =
                                               (ed.FStar_Syntax_Syntax.mname);
                                             FStar_Syntax_Syntax.result_typ =
                                               res_typ;
                                             FStar_Syntax_Syntax.effect_args
                                               = uu____7234;
                                             FStar_Syntax_Syntax.flags = []
                                           }  in
                                         FStar_Syntax_Syntax.mk_Comp
                                           uu____7231
                                          in
                                       FStar_All.pipe_right uu____7230
                                         FStar_TypeChecker_Common.lcomp_of_comp
                                        in
                                     let e3 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_app
                                            (reflect_op, [(e2, aqual)]))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     let uu____7305 =
                                       comp_check_expected_typ env1 e3 c  in
                                     (match uu____7305 with
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
                                          let uu____7328 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g' g
                                             in
                                          (e5, c1, uu____7328))))))))
       | FStar_Syntax_Syntax.Tm_app
           (head1,(tau,FStar_Pervasives_Native.None )::[]) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7367 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7367 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app
           (head1,(uu____7417,FStar_Pervasives_Native.Some
                   (FStar_Syntax_Syntax.Implicit uu____7418))::(tau,FStar_Pervasives_Native.None
                                                                )::[])
           when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7471 = FStar_Syntax_Util.head_and_args top  in
           (match uu____7471 with
            | (head2,args) ->
                tc_synth head2 env1 args top.FStar_Syntax_Syntax.pos)
       | FStar_Syntax_Syntax.Tm_app (head1,args) when
           (FStar_Syntax_Util.is_synth_by_tactic head1) &&
             (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
           ->
           let uu____7546 =
             match args with
             | (tau,FStar_Pervasives_Native.None )::rest ->
                 ([(tau, FStar_Pervasives_Native.None)], rest)
             | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                b))::(tau,FStar_Pervasives_Native.None )::rest ->
                 ([(a,
                     (FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit b)));
                  (tau, FStar_Pervasives_Native.None)], rest)
             | uu____7756 ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_SynthByTacticError,
                     "synth_by_tactic: bad application")
                   top.FStar_Syntax_Syntax.pos
              in
           (match uu____7546 with
            | (args1,args2) ->
                let t1 = FStar_Syntax_Util.mk_app head1 args1  in
                let t2 = FStar_Syntax_Util.mk_app t1 args2  in
                tc_term env1 t2)
       | FStar_Syntax_Syntax.Tm_app (head1,args) ->
           let env0 = env1  in
           let env2 =
             let uu____7875 =
               let uu____7876 = FStar_TypeChecker_Env.clear_expected_typ env1
                  in
               FStar_All.pipe_right uu____7876 FStar_Pervasives_Native.fst
                in
             FStar_All.pipe_right uu____7875 instantiate_both  in
           ((let uu____7892 =
               FStar_TypeChecker_Env.debug env2 FStar_Options.High  in
             if uu____7892
             then
               let uu____7895 =
                 FStar_Range.string_of_range top.FStar_Syntax_Syntax.pos  in
               let uu____7897 = FStar_Syntax_Print.term_to_string top  in
               let uu____7899 =
                 let uu____7901 = FStar_TypeChecker_Env.expected_typ env0  in
                 FStar_All.pipe_right uu____7901
                   (fun uu___3_7908  ->
                      match uu___3_7908 with
                      | FStar_Pervasives_Native.None  -> "none"
                      | FStar_Pervasives_Native.Some t ->
                          FStar_Syntax_Print.term_to_string t)
                  in
               FStar_Util.print3
                 "(%s) Checking app %s, expected type is %s\n" uu____7895
                 uu____7897 uu____7899
             else ());
            (let uu____7917 = tc_term (no_inst env2) head1  in
             match uu____7917 with
             | (head2,chead,g_head) ->
                 let uu____7933 =
                   let uu____7938 = FStar_TypeChecker_Common.lcomp_comp chead
                      in
                   FStar_All.pipe_right uu____7938
                     (fun uu____7955  ->
                        match uu____7955 with
                        | (c,g) ->
                            let uu____7966 =
                              FStar_TypeChecker_Env.conj_guard g_head g  in
                            (c, uu____7966))
                    in
                 (match uu____7933 with
                  | (chead1,g_head1) ->
                      let uu____7975 =
                        let uu____7982 =
                          ((Prims.op_Negation env2.FStar_TypeChecker_Env.lax)
                             &&
                             (let uu____7985 = FStar_Options.lax ()  in
                              Prims.op_Negation uu____7985))
                            &&
                            (FStar_TypeChecker_Util.short_circuit_head head2)
                           in
                        if uu____7982
                        then
                          let uu____7994 =
                            let uu____8001 =
                              FStar_TypeChecker_Env.expected_typ env0  in
                            check_short_circuit_args env2 head2 chead1
                              g_head1 args uu____8001
                             in
                          match uu____7994 with | (e1,c,g) -> (e1, c, g)
                        else
                          (let uu____8015 =
                             FStar_TypeChecker_Env.expected_typ env0  in
                           check_application_args env2 head2 chead1 g_head1
                             args uu____8015)
                         in
                      (match uu____7975 with
                       | (e1,c,g) ->
                           let uu____8027 =
                             let uu____8034 =
                               FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                 c
                                in
                             if uu____8034
                             then
                               let uu____8043 =
                                 FStar_TypeChecker_Util.maybe_instantiate
                                   env0 e1 c.FStar_TypeChecker_Common.res_typ
                                  in
                               match uu____8043 with
                               | (e2,res_typ,implicits) ->
                                   let uu____8059 =
                                     FStar_TypeChecker_Common.set_result_typ_lc
                                       c res_typ
                                      in
                                   (e2, uu____8059, implicits)
                             else
                               (e1, c, FStar_TypeChecker_Env.trivial_guard)
                              in
                           (match uu____8027 with
                            | (e2,c1,implicits) ->
                                ((let uu____8072 =
                                    FStar_TypeChecker_Env.debug env2
                                      FStar_Options.Extreme
                                     in
                                  if uu____8072
                                  then
                                    let uu____8075 =
                                      FStar_TypeChecker_Rel.print_pending_implicits
                                        g
                                       in
                                    FStar_Util.print1
                                      "Introduced {%s} implicits in application\n"
                                      uu____8075
                                  else ());
                                 (let uu____8080 =
                                    comp_check_expected_typ env0 e2 c1  in
                                  match uu____8080 with
                                  | (e3,c2,g') ->
                                      let gres =
                                        FStar_TypeChecker_Env.conj_guard g g'
                                         in
                                      let gres1 =
                                        FStar_TypeChecker_Env.conj_guard gres
                                          implicits
                                         in
                                      ((let uu____8099 =
                                          FStar_TypeChecker_Env.debug env2
                                            FStar_Options.Extreme
                                           in
                                        if uu____8099
                                        then
                                          let uu____8102 =
                                            FStar_Syntax_Print.term_to_string
                                              e3
                                             in
                                          let uu____8104 =
                                            FStar_TypeChecker_Rel.guard_to_string
                                              env2 gres1
                                             in
                                          FStar_Util.print2
                                            "Guard from application node %s is %s\n"
                                            uu____8102 uu____8104
                                        else ());
                                       (e3, c2, gres1)))))))))
       | FStar_Syntax_Syntax.Tm_match (e1,eqns) ->
           let uu____8147 = FStar_TypeChecker_Env.clear_expected_typ env1  in
           (match uu____8147 with
            | (env11,topt) ->
                let env12 = instantiate_both env11  in
                let uu____8167 = tc_term env12 e1  in
                (match uu____8167 with
                 | (e11,c1,g1) ->
                     let uu____8183 =
                       match topt with
                       | FStar_Pervasives_Native.Some t -> (env1, t, g1)
                       | FStar_Pervasives_Native.None  ->
                           let uu____8197 = FStar_Syntax_Util.type_u ()  in
                           (match uu____8197 with
                            | (k,uu____8209) ->
                                let uu____8210 =
                                  FStar_TypeChecker_Util.new_implicit_var
                                    "match result" e.FStar_Syntax_Syntax.pos
                                    env1 k
                                   in
                                (match uu____8210 with
                                 | (res_t,uu____8231,g) ->
                                     let uu____8245 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         env1 res_t
                                        in
                                     let uu____8246 =
                                       FStar_TypeChecker_Env.conj_guard g1 g
                                        in
                                     (uu____8245, res_t, uu____8246)))
                        in
                     (match uu____8183 with
                      | (env_branches,res_t,g11) ->
                          ((let uu____8257 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Extreme
                               in
                            if uu____8257
                            then
                              let uu____8260 =
                                FStar_Syntax_Print.term_to_string res_t  in
                              FStar_Util.print1
                                "Tm_match: expected type of branches is %s\n"
                                uu____8260
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
                            let uu____8396 =
                              let uu____8404 =
                                FStar_List.fold_right
                                  (fun uu____8497  ->
                                     fun uu____8498  ->
                                       match (uu____8497, uu____8498) with
                                       | ((branch1,f,eff_label,cflags,c,g,erasable_branch),
                                          (caccum,gaccum,erasable1)) ->
                                           let uu____8770 =
                                             FStar_TypeChecker_Env.conj_guard
                                               g gaccum
                                              in
                                           (((f, eff_label, cflags, c) ::
                                             caccum), uu____8770,
                                             (erasable1 || erasable_branch)))
                                  t_eqns
                                  ([], FStar_TypeChecker_Env.trivial_guard,
                                    false)
                                 in
                              match uu____8404 with
                              | (cases,g,erasable1) ->
                                  let uu____8884 =
                                    FStar_TypeChecker_Util.bind_cases env1
                                      res_t cases
                                     in
                                  (uu____8884, g, erasable1)
                               in
                            match uu____8396 with
                            | (c_branches,g_branches,erasable1) ->
                                let cres =
                                  FStar_TypeChecker_Util.bind
                                    e11.FStar_Syntax_Syntax.pos env1
                                    (FStar_Pervasives_Native.Some e11) c1
                                    ((FStar_Pervasives_Native.Some guard_x),
                                      c_branches)
                                   in
                                let cres1 =
                                  if erasable1
                                  then
                                    let e2 = FStar_Syntax_Util.exp_true_bool
                                       in
                                    let c =
                                      FStar_Syntax_Syntax.mk_GTotal'
                                        FStar_Syntax_Util.t_bool
                                        (FStar_Pervasives_Native.Some
                                           FStar_Syntax_Syntax.U_zero)
                                       in
                                    let uu____8904 =
                                      FStar_TypeChecker_Common.lcomp_of_comp
                                        c
                                       in
                                    FStar_TypeChecker_Util.bind
                                      e2.FStar_Syntax_Syntax.pos env1
                                      (FStar_Pervasives_Native.Some e2)
                                      uu____8904
                                      (FStar_Pervasives_Native.None, cres)
                                  else cres  in
                                let e2 =
                                  let mk_match scrutinee =
                                    let branches =
                                      FStar_All.pipe_right t_eqns
                                        (FStar_List.map
                                           (fun uu____9046  ->
                                              match uu____9046 with
                                              | ((pat,wopt,br),uu____9094,eff_label,uu____9096,uu____9097,uu____9098,uu____9099)
                                                  ->
                                                  let uu____9138 =
                                                    FStar_TypeChecker_Util.maybe_lift
                                                      env1 br eff_label
                                                      cres1.FStar_TypeChecker_Common.eff_name
                                                      res_t
                                                     in
                                                  (pat, wopt, uu____9138)))
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
                                        cres1.FStar_TypeChecker_Common.eff_name
                                        cres1.FStar_TypeChecker_Common.res_typ
                                       in
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_ascribed
                                         (e3,
                                           ((FStar_Util.Inl
                                               (cres1.FStar_TypeChecker_Common.res_typ)),
                                             FStar_Pervasives_Native.None),
                                           (FStar_Pervasives_Native.Some
                                              (cres1.FStar_TypeChecker_Common.eff_name))))
                                      FStar_Pervasives_Native.None
                                      e3.FStar_Syntax_Syntax.pos
                                     in
                                  let uu____9205 =
                                    FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                      env1
                                      c1.FStar_TypeChecker_Common.eff_name
                                     in
                                  if uu____9205
                                  then mk_match e11
                                  else
                                    (let e_match =
                                       let uu____9213 =
                                         FStar_Syntax_Syntax.bv_to_name
                                           guard_x
                                          in
                                       mk_match uu____9213  in
                                     let lb =
                                       let uu____9217 =
                                         FStar_TypeChecker_Env.norm_eff_name
                                           env1
                                           c1.FStar_TypeChecker_Common.eff_name
                                          in
                                       FStar_Syntax_Util.mk_letbinding
                                         (FStar_Util.Inl guard_x) []
                                         c1.FStar_TypeChecker_Common.res_typ
                                         uu____9217 e11 []
                                         e11.FStar_Syntax_Syntax.pos
                                        in
                                     let e2 =
                                       let uu____9223 =
                                         let uu____9230 =
                                           let uu____9231 =
                                             let uu____9245 =
                                               let uu____9248 =
                                                 let uu____9249 =
                                                   FStar_Syntax_Syntax.mk_binder
                                                     guard_x
                                                    in
                                                 [uu____9249]  in
                                               FStar_Syntax_Subst.close
                                                 uu____9248 e_match
                                                in
                                             ((false, [lb]), uu____9245)  in
                                           FStar_Syntax_Syntax.Tm_let
                                             uu____9231
                                            in
                                         FStar_Syntax_Syntax.mk uu____9230
                                          in
                                       uu____9223
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     FStar_TypeChecker_Util.maybe_monadic
                                       env1 e2
                                       cres1.FStar_TypeChecker_Common.eff_name
                                       cres1.FStar_TypeChecker_Common.res_typ)
                                   in
                                ((let uu____9282 =
                                    FStar_TypeChecker_Env.debug env1
                                      FStar_Options.Extreme
                                     in
                                  if uu____9282
                                  then
                                    let uu____9285 =
                                      FStar_Range.string_of_range
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let uu____9287 =
                                      FStar_TypeChecker_Common.lcomp_to_string
                                        cres1
                                       in
                                    FStar_Util.print2
                                      "(%s) Typechecked Tm_match, comp type = %s\n"
                                      uu____9285 uu____9287
                                  else ());
                                 (let uu____9292 =
                                    FStar_TypeChecker_Env.conj_guard g11
                                      g_branches
                                     in
                                  (e2, cres1, uu____9292))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9293;
                FStar_Syntax_Syntax.lbunivs = uu____9294;
                FStar_Syntax_Syntax.lbtyp = uu____9295;
                FStar_Syntax_Syntax.lbeff = uu____9296;
                FStar_Syntax_Syntax.lbdef = uu____9297;
                FStar_Syntax_Syntax.lbattrs = uu____9298;
                FStar_Syntax_Syntax.lbpos = uu____9299;_}::[]),uu____9300)
           -> check_top_level_let env1 top
       | FStar_Syntax_Syntax.Tm_let ((false ,uu____9326),uu____9327) ->
           check_inner_let env1 top
       | FStar_Syntax_Syntax.Tm_let
           ((true
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr uu____9345;
                FStar_Syntax_Syntax.lbunivs = uu____9346;
                FStar_Syntax_Syntax.lbtyp = uu____9347;
                FStar_Syntax_Syntax.lbeff = uu____9348;
                FStar_Syntax_Syntax.lbdef = uu____9349;
                FStar_Syntax_Syntax.lbattrs = uu____9350;
                FStar_Syntax_Syntax.lbpos = uu____9351;_}::uu____9352),uu____9353)
           -> check_top_level_let_rec env1 top
       | FStar_Syntax_Syntax.Tm_let ((true ,uu____9381),uu____9382) ->
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
          let uu____9416 =
            match args with
            | (tau,FStar_Pervasives_Native.None )::[] ->
                (tau, FStar_Pervasives_Native.None)
            | (a,FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
               uu____9455))::(tau,FStar_Pervasives_Native.None )::[] ->
                (tau, (FStar_Pervasives_Native.Some a))
            | uu____9496 ->
                FStar_Errors.raise_error
                  (FStar_Errors.Fatal_SynthByTacticError,
                    "synth_by_tactic: bad application") rng
             in
          match uu____9416 with
          | (tau,atyp) ->
              let typ =
                match atyp with
                | FStar_Pervasives_Native.Some t -> t
                | FStar_Pervasives_Native.None  ->
                    let uu____9529 = FStar_TypeChecker_Env.expected_typ env
                       in
                    (match uu____9529 with
                     | FStar_Pervasives_Native.Some t -> t
                     | FStar_Pervasives_Native.None  ->
                         let uu____9533 = FStar_TypeChecker_Env.get_range env
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_SynthByTacticError,
                             "synth_by_tactic: need a type annotation when no expected type is present")
                           uu____9533)
                 in
              let uu____9536 =
                let uu____9543 =
                  let uu____9544 =
                    let uu____9545 = FStar_Syntax_Util.type_u ()  in
                    FStar_All.pipe_left FStar_Pervasives_Native.fst
                      uu____9545
                     in
                  FStar_TypeChecker_Env.set_expected_typ env uu____9544  in
                tc_term uu____9543 typ  in
              (match uu____9536 with
               | (typ1,uu____9561,g1) ->
                   (FStar_TypeChecker_Rel.force_trivial_guard env g1;
                    (let uu____9564 = tc_tactic env tau  in
                     match uu____9564 with
                     | (tau1,uu____9578,g2) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env g2;
                          (let t =
                             env.FStar_TypeChecker_Env.synth_hook env typ1
                               (let uu___1243_9583 = tau1  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1243_9583.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos = rng;
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1243_9583.FStar_Syntax_Syntax.vars)
                                })
                              in
                           (let uu____9585 =
                              FStar_All.pipe_left
                                (FStar_TypeChecker_Env.debug env)
                                (FStar_Options.Other "Tac")
                               in
                            if uu____9585
                            then
                              let uu____9590 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print1 "Got %s\n" uu____9590
                            else ());
                           FStar_TypeChecker_Util.check_uvars
                             tau1.FStar_Syntax_Syntax.pos t;
                           (let uu____9596 =
                              let uu____9597 =
                                FStar_Syntax_Syntax.mk_Total typ1  in
                              FStar_All.pipe_left
                                FStar_TypeChecker_Common.lcomp_of_comp
                                uu____9597
                               in
                            (t, uu____9596,
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
        let uu___1251_9601 = env  in
        {
          FStar_TypeChecker_Env.solver =
            (uu___1251_9601.FStar_TypeChecker_Env.solver);
          FStar_TypeChecker_Env.range =
            (uu___1251_9601.FStar_TypeChecker_Env.range);
          FStar_TypeChecker_Env.curmodule =
            (uu___1251_9601.FStar_TypeChecker_Env.curmodule);
          FStar_TypeChecker_Env.gamma =
            (uu___1251_9601.FStar_TypeChecker_Env.gamma);
          FStar_TypeChecker_Env.gamma_sig =
            (uu___1251_9601.FStar_TypeChecker_Env.gamma_sig);
          FStar_TypeChecker_Env.gamma_cache =
            (uu___1251_9601.FStar_TypeChecker_Env.gamma_cache);
          FStar_TypeChecker_Env.modules =
            (uu___1251_9601.FStar_TypeChecker_Env.modules);
          FStar_TypeChecker_Env.expected_typ =
            (uu___1251_9601.FStar_TypeChecker_Env.expected_typ);
          FStar_TypeChecker_Env.sigtab =
            (uu___1251_9601.FStar_TypeChecker_Env.sigtab);
          FStar_TypeChecker_Env.attrtab =
            (uu___1251_9601.FStar_TypeChecker_Env.attrtab);
          FStar_TypeChecker_Env.is_pattern =
            (uu___1251_9601.FStar_TypeChecker_Env.is_pattern);
          FStar_TypeChecker_Env.instantiate_imp =
            (uu___1251_9601.FStar_TypeChecker_Env.instantiate_imp);
          FStar_TypeChecker_Env.effects =
            (uu___1251_9601.FStar_TypeChecker_Env.effects);
          FStar_TypeChecker_Env.generalize =
            (uu___1251_9601.FStar_TypeChecker_Env.generalize);
          FStar_TypeChecker_Env.letrecs =
            (uu___1251_9601.FStar_TypeChecker_Env.letrecs);
          FStar_TypeChecker_Env.top_level =
            (uu___1251_9601.FStar_TypeChecker_Env.top_level);
          FStar_TypeChecker_Env.check_uvars =
            (uu___1251_9601.FStar_TypeChecker_Env.check_uvars);
          FStar_TypeChecker_Env.use_eq =
            (uu___1251_9601.FStar_TypeChecker_Env.use_eq);
          FStar_TypeChecker_Env.is_iface =
            (uu___1251_9601.FStar_TypeChecker_Env.is_iface);
          FStar_TypeChecker_Env.admit =
            (uu___1251_9601.FStar_TypeChecker_Env.admit);
          FStar_TypeChecker_Env.lax =
            (uu___1251_9601.FStar_TypeChecker_Env.lax);
          FStar_TypeChecker_Env.lax_universes =
            (uu___1251_9601.FStar_TypeChecker_Env.lax_universes);
          FStar_TypeChecker_Env.phase1 =
            (uu___1251_9601.FStar_TypeChecker_Env.phase1);
          FStar_TypeChecker_Env.failhard = true;
          FStar_TypeChecker_Env.nosynth =
            (uu___1251_9601.FStar_TypeChecker_Env.nosynth);
          FStar_TypeChecker_Env.uvar_subtyping =
            (uu___1251_9601.FStar_TypeChecker_Env.uvar_subtyping);
          FStar_TypeChecker_Env.tc_term =
            (uu___1251_9601.FStar_TypeChecker_Env.tc_term);
          FStar_TypeChecker_Env.type_of =
            (uu___1251_9601.FStar_TypeChecker_Env.type_of);
          FStar_TypeChecker_Env.universe_of =
            (uu___1251_9601.FStar_TypeChecker_Env.universe_of);
          FStar_TypeChecker_Env.check_type_of =
            (uu___1251_9601.FStar_TypeChecker_Env.check_type_of);
          FStar_TypeChecker_Env.use_bv_sorts =
            (uu___1251_9601.FStar_TypeChecker_Env.use_bv_sorts);
          FStar_TypeChecker_Env.qtbl_name_and_index =
            (uu___1251_9601.FStar_TypeChecker_Env.qtbl_name_and_index);
          FStar_TypeChecker_Env.normalized_eff_names =
            (uu___1251_9601.FStar_TypeChecker_Env.normalized_eff_names);
          FStar_TypeChecker_Env.fv_delta_depths =
            (uu___1251_9601.FStar_TypeChecker_Env.fv_delta_depths);
          FStar_TypeChecker_Env.proof_ns =
            (uu___1251_9601.FStar_TypeChecker_Env.proof_ns);
          FStar_TypeChecker_Env.synth_hook =
            (uu___1251_9601.FStar_TypeChecker_Env.synth_hook);
          FStar_TypeChecker_Env.try_solve_implicits_hook =
            (uu___1251_9601.FStar_TypeChecker_Env.try_solve_implicits_hook);
          FStar_TypeChecker_Env.splice =
            (uu___1251_9601.FStar_TypeChecker_Env.splice);
          FStar_TypeChecker_Env.postprocess =
            (uu___1251_9601.FStar_TypeChecker_Env.postprocess);
          FStar_TypeChecker_Env.is_native_tactic =
            (uu___1251_9601.FStar_TypeChecker_Env.is_native_tactic);
          FStar_TypeChecker_Env.identifier_info =
            (uu___1251_9601.FStar_TypeChecker_Env.identifier_info);
          FStar_TypeChecker_Env.tc_hooks =
            (uu___1251_9601.FStar_TypeChecker_Env.tc_hooks);
          FStar_TypeChecker_Env.dsenv =
            (uu___1251_9601.FStar_TypeChecker_Env.dsenv);
          FStar_TypeChecker_Env.nbe =
            (uu___1251_9601.FStar_TypeChecker_Env.nbe);
          FStar_TypeChecker_Env.strict_args_tab =
            (uu___1251_9601.FStar_TypeChecker_Env.strict_args_tab);
          FStar_TypeChecker_Env.erasable_types_tab =
            (uu___1251_9601.FStar_TypeChecker_Env.erasable_types_tab)
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
          let uu____9624 = tc_tactic env tactic  in
          (match uu____9624 with
           | (tactic1,uu____9638,g) ->
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
        let uu____9690 = FStar_TypeChecker_Util.maybe_instantiate env1 e1 t0
           in
        match uu____9690 with
        | (e2,t,implicits) ->
            let tc =
              let uu____9711 = FStar_TypeChecker_Env.should_verify env1  in
              if uu____9711
              then FStar_Util.Inl t
              else
                (let uu____9720 =
                   let uu____9721 = FStar_Syntax_Syntax.mk_Total t  in
                   FStar_All.pipe_left FStar_TypeChecker_Common.lcomp_of_comp
                     uu____9721
                    in
                 FStar_Util.Inr uu____9720)
               in
            let is_data_ctor uu___4_9730 =
              match uu___4_9730 with
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor )
                  -> true
              | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
                  uu____9735) -> true
              | uu____9743 -> false  in
            let uu____9747 =
              (is_data_ctor dc) &&
                (let uu____9750 =
                   FStar_TypeChecker_Env.is_datacon env1
                     v1.FStar_Syntax_Syntax.v
                    in
                 Prims.op_Negation uu____9750)
               in
            if uu____9747
            then
              let uu____9759 =
                let uu____9765 =
                  FStar_Util.format1 "Expected a data constructor; got %s"
                    (v1.FStar_Syntax_Syntax.v).FStar_Ident.str
                   in
                (FStar_Errors.Fatal_MissingDataConstructor, uu____9765)  in
              let uu____9769 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____9759 uu____9769
            else value_check_expected_typ env1 e2 tc implicits
         in
      let env1 =
        FStar_TypeChecker_Env.set_range env e.FStar_Syntax_Syntax.pos  in
      let top = FStar_Syntax_Subst.compress e  in
      match top.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_bvar x ->
          let uu____9787 =
            let uu____9789 = FStar_Syntax_Print.term_to_string top  in
            FStar_Util.format1
              "Impossible: Violation of locally nameless convention: %s"
              uu____9789
             in
          failwith uu____9787
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____9816 =
            let uu____9821 =
              FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
               in
            FStar_Util.Inl uu____9821  in
          value_check_expected_typ env1 e uu____9816
            FStar_TypeChecker_Env.trivial_guard
      | FStar_Syntax_Syntax.Tm_unknown  ->
          let r = FStar_TypeChecker_Env.get_range env1  in
          let uu____9823 =
            let uu____9836 = FStar_TypeChecker_Env.expected_typ env1  in
            match uu____9836 with
            | FStar_Pervasives_Native.None  ->
                let uu____9851 = FStar_Syntax_Util.type_u ()  in
                (match uu____9851 with
                 | (k,u) ->
                     FStar_TypeChecker_Util.new_implicit_var
                       "type of user-provided implicit term" r env1 k)
            | FStar_Pervasives_Native.Some t ->
                (t, [], FStar_TypeChecker_Env.trivial_guard)
             in
          (match uu____9823 with
           | (t,uu____9889,g0) ->
               let uu____9903 =
                 let uu____9916 =
                   let uu____9918 = FStar_Range.string_of_range r  in
                   Prims.op_Hat "user-provided implicit term at " uu____9918
                    in
                 FStar_TypeChecker_Util.new_implicit_var uu____9916 r env1 t
                  in
               (match uu____9903 with
                | (e1,uu____9928,g1) ->
                    let uu____9942 =
                      let uu____9943 = FStar_Syntax_Syntax.mk_Total t  in
                      FStar_All.pipe_right uu____9943
                        FStar_TypeChecker_Common.lcomp_of_comp
                       in
                    let uu____9944 = FStar_TypeChecker_Env.conj_guard g0 g1
                       in
                    (e1, uu____9942, uu____9944)))
      | FStar_Syntax_Syntax.Tm_name x ->
          let uu____9946 =
            if env1.FStar_TypeChecker_Env.use_bv_sorts
            then
              let uu____9956 = FStar_Syntax_Syntax.range_of_bv x  in
              ((x.FStar_Syntax_Syntax.sort), uu____9956)
            else FStar_TypeChecker_Env.lookup_bv env1 x  in
          (match uu____9946 with
           | (t,rng) ->
               let x1 =
                 FStar_Syntax_Syntax.set_range_of_bv
                   (let uu___1316_9970 = x  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___1316_9970.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___1316_9970.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = t
                    }) rng
                  in
               (FStar_TypeChecker_Env.insert_bv_info env1 x1 t;
                (let e1 = FStar_Syntax_Syntax.bv_to_name x1  in
                 let uu____9973 =
                   FStar_TypeChecker_Util.maybe_instantiate env1 e1 t  in
                 match uu____9973 with
                 | (e2,t1,implicits) ->
                     let tc =
                       let uu____9994 =
                         FStar_TypeChecker_Env.should_verify env1  in
                       if uu____9994
                       then FStar_Util.Inl t1
                       else
                         (let uu____10003 =
                            let uu____10004 = FStar_Syntax_Syntax.mk_Total t1
                               in
                            FStar_All.pipe_left
                              FStar_TypeChecker_Common.lcomp_of_comp
                              uu____10004
                             in
                          FStar_Util.Inr uu____10003)
                        in
                     value_check_expected_typ env1 e2 tc implicits)))
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10006;
             FStar_Syntax_Syntax.vars = uu____10007;_},uu____10008)
          when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10013 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10013
      | FStar_Syntax_Syntax.Tm_fvar fv when
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.synth_lid) &&
            (Prims.op_Negation env1.FStar_TypeChecker_Env.phase1)
          ->
          let uu____10023 = FStar_TypeChecker_Env.get_range env1  in
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_BadlyInstantiatedSynthByTactic,
              "Badly instantiated synth_by_tactic") uu____10023
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____10033;
             FStar_Syntax_Syntax.vars = uu____10034;_},us)
          ->
          let us1 = FStar_List.map (tc_universe env1) us  in
          let uu____10043 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10043 with
           | ((us',t),range) ->
               (if (FStar_List.length us1) <> (FStar_List.length us')
                then
                  (let uu____10067 =
                     let uu____10073 =
                       let uu____10075 = FStar_Syntax_Print.fv_to_string fv
                          in
                       let uu____10077 =
                         FStar_Util.string_of_int (FStar_List.length us1)  in
                       let uu____10079 =
                         FStar_Util.string_of_int (FStar_List.length us')  in
                       FStar_Util.format3
                         "Unexpected number of universe instantiations for \"%s\" (%s vs %s)"
                         uu____10075 uu____10077 uu____10079
                        in
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       uu____10073)
                      in
                   let uu____10083 = FStar_TypeChecker_Env.get_range env1  in
                   FStar_Errors.raise_error uu____10067 uu____10083)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____10100 -> failwith "Impossible") us' us1;
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10105 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10105 us1  in
                  check_instantiated_fvar env1
                    fv'.FStar_Syntax_Syntax.fv_name
                    fv'.FStar_Syntax_Syntax.fv_qual e1 t))))
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____10107 =
            FStar_TypeChecker_Env.lookup_lid env1
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____10107 with
           | ((us,t),range) ->
               ((let uu____10130 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
                     (FStar_Options.Other "Range")
                    in
                 if uu____10130
                 then
                   let uu____10135 =
                     let uu____10137 = FStar_Syntax_Syntax.lid_of_fv fv  in
                     FStar_Syntax_Print.lid_to_string uu____10137  in
                   let uu____10138 =
                     FStar_Range.string_of_range e.FStar_Syntax_Syntax.pos
                      in
                   let uu____10140 = FStar_Range.string_of_range range  in
                   let uu____10142 = FStar_Range.string_of_use_range range
                      in
                   let uu____10144 = FStar_Syntax_Print.term_to_string t  in
                   FStar_Util.print5
                     "Lookup up fvar %s at location %s (lid range = defined at %s, used at %s); got universes type %s"
                     uu____10135 uu____10138 uu____10140 uu____10142
                     uu____10144
                 else ());
                (let fv' = FStar_Syntax_Syntax.set_range_of_fv fv range  in
                 FStar_TypeChecker_Env.insert_fv_info env1 fv' t;
                 (let e1 =
                    let uu____10152 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_fvar fv')
                        FStar_Pervasives_Native.None
                        e.FStar_Syntax_Syntax.pos
                       in
                    FStar_Syntax_Syntax.mk_Tm_uinst uu____10152 us  in
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
          let uu____10180 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____10180 with
           | (bs1,c1) ->
               let env0 = env1  in
               let uu____10194 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10194 with
                | (env2,uu____10208) ->
                    let uu____10213 = tc_binders env2 bs1  in
                    (match uu____10213 with
                     | (bs2,env3,g,us) ->
                         let uu____10232 = tc_comp env3 c1  in
                         (match uu____10232 with
                          | (c2,uc,f) ->
                              let e1 =
                                let uu___1396_10251 =
                                  FStar_Syntax_Util.arrow bs2 c2  in
                                {
                                  FStar_Syntax_Syntax.n =
                                    (uu___1396_10251.FStar_Syntax_Syntax.n);
                                  FStar_Syntax_Syntax.pos =
                                    (top.FStar_Syntax_Syntax.pos);
                                  FStar_Syntax_Syntax.vars =
                                    (uu___1396_10251.FStar_Syntax_Syntax.vars)
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
                                  let uu____10262 =
                                    FStar_TypeChecker_Env.close_guard_univs
                                      us bs2 f
                                     in
                                  FStar_TypeChecker_Env.conj_guard g
                                    uu____10262
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
          let uu____10278 =
            let uu____10283 =
              let uu____10284 = FStar_Syntax_Syntax.mk_binder x  in
              [uu____10284]  in
            FStar_Syntax_Subst.open_term uu____10283 phi  in
          (match uu____10278 with
           | (x1,phi1) ->
               let env0 = env1  in
               let uu____10312 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____10312 with
                | (env2,uu____10326) ->
                    let uu____10331 =
                      let uu____10346 = FStar_List.hd x1  in
                      tc_binder env2 uu____10346  in
                    (match uu____10331 with
                     | (x2,env3,f1,u) ->
                         ((let uu____10382 =
                             FStar_TypeChecker_Env.debug env3
                               FStar_Options.High
                              in
                           if uu____10382
                           then
                             let uu____10385 =
                               FStar_Range.string_of_range
                                 top.FStar_Syntax_Syntax.pos
                                in
                             let uu____10387 =
                               FStar_Syntax_Print.term_to_string phi1  in
                             let uu____10389 =
                               FStar_Syntax_Print.bv_to_string
                                 (FStar_Pervasives_Native.fst x2)
                                in
                             FStar_Util.print3
                               "(%s) Checking refinement formula %s; binder is %s\n"
                               uu____10385 uu____10387 uu____10389
                           else ());
                          (let uu____10396 = FStar_Syntax_Util.type_u ()  in
                           match uu____10396 with
                           | (t_phi,uu____10408) ->
                               let uu____10409 =
                                 tc_check_tot_or_gtot_term env3 phi1 t_phi
                                  in
                               (match uu____10409 with
                                | (phi2,uu____10423,f2) ->
                                    let e1 =
                                      let uu___1434_10428 =
                                        FStar_Syntax_Util.refine
                                          (FStar_Pervasives_Native.fst x2)
                                          phi2
                                         in
                                      {
                                        FStar_Syntax_Syntax.n =
                                          (uu___1434_10428.FStar_Syntax_Syntax.n);
                                        FStar_Syntax_Syntax.pos =
                                          (top.FStar_Syntax_Syntax.pos);
                                        FStar_Syntax_Syntax.vars =
                                          (uu___1434_10428.FStar_Syntax_Syntax.vars)
                                      }  in
                                    let t =
                                      FStar_Syntax_Syntax.mk
                                        (FStar_Syntax_Syntax.Tm_type u)
                                        FStar_Pervasives_Native.None
                                        top.FStar_Syntax_Syntax.pos
                                       in
                                    let g =
                                      let uu____10437 =
                                        FStar_TypeChecker_Env.close_guard_univs
                                          [u] [x2] f2
                                         in
                                      FStar_TypeChecker_Env.conj_guard f1
                                        uu____10437
                                       in
                                    let g1 =
                                      FStar_TypeChecker_Util.close_guard_implicits
                                        env3 [x2] g
                                       in
                                    value_check_expected_typ env0 e1
                                      (FStar_Util.Inl t) g1))))))
      | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____10465) ->
          let bs1 = FStar_TypeChecker_Util.maybe_add_implicit_binders env1 bs
             in
          ((let uu____10492 =
              FStar_TypeChecker_Env.debug env1 FStar_Options.Medium  in
            if uu____10492
            then
              let uu____10495 =
                FStar_Syntax_Print.term_to_string
                  (let uu___1447_10499 = top  in
                   {
                     FStar_Syntax_Syntax.n =
                       (FStar_Syntax_Syntax.Tm_abs
                          (bs1, body, FStar_Pervasives_Native.None));
                     FStar_Syntax_Syntax.pos =
                       (uu___1447_10499.FStar_Syntax_Syntax.pos);
                     FStar_Syntax_Syntax.vars =
                       (uu___1447_10499.FStar_Syntax_Syntax.vars)
                   })
                 in
              FStar_Util.print1 "Abstraction is: %s\n" uu____10495
            else ());
           (let uu____10515 = FStar_Syntax_Subst.open_term bs1 body  in
            match uu____10515 with | (bs2,body1) -> tc_abs env1 top bs2 body1))
      | uu____10528 ->
          let uu____10529 =
            let uu____10531 = FStar_Syntax_Print.term_to_string top  in
            let uu____10533 = FStar_Syntax_Print.tag_of_term top  in
            FStar_Util.format2 "Unexpected value: %s (%s)" uu____10531
              uu____10533
             in
          failwith uu____10529

and (tc_constant :
  FStar_TypeChecker_Env.env ->
    FStar_Range.range -> FStar_Const.sconst -> FStar_Syntax_Syntax.typ)
  =
  fun env  ->
    fun r  ->
      fun c  ->
        match c with
        | FStar_Const.Const_unit  -> FStar_Syntax_Syntax.t_unit
        | FStar_Const.Const_bool uu____10545 -> FStar_Syntax_Util.t_bool
        | FStar_Const.Const_int (uu____10547,FStar_Pervasives_Native.None )
            -> FStar_Syntax_Syntax.t_int
        | FStar_Const.Const_int
            (uu____10560,FStar_Pervasives_Native.Some msize) ->
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
        | FStar_Const.Const_string uu____10578 ->
            FStar_Syntax_Syntax.t_string
        | FStar_Const.Const_real uu____10584 -> FStar_Syntax_Syntax.t_real
        | FStar_Const.Const_float uu____10586 -> FStar_Syntax_Syntax.t_float
        | FStar_Const.Const_char uu____10587 ->
            let uu____10589 =
              FStar_Syntax_DsEnv.try_lookup_lid
                env.FStar_TypeChecker_Env.dsenv FStar_Parser_Const.char_lid
               in
            FStar_All.pipe_right uu____10589 FStar_Util.must
        | FStar_Const.Const_effect  -> FStar_Syntax_Util.ktype0
        | FStar_Const.Const_range uu____10594 -> FStar_Syntax_Syntax.t_range
        | FStar_Const.Const_range_of  ->
            let uu____10595 =
              let uu____10601 =
                let uu____10603 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10603
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10601)  in
            FStar_Errors.raise_error uu____10595 r
        | FStar_Const.Const_set_range_of  ->
            let uu____10607 =
              let uu____10613 =
                let uu____10615 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10615
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10613)  in
            FStar_Errors.raise_error uu____10607 r
        | FStar_Const.Const_reify  ->
            let uu____10619 =
              let uu____10625 =
                let uu____10627 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10627
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10625)  in
            FStar_Errors.raise_error uu____10619 r
        | FStar_Const.Const_reflect uu____10631 ->
            let uu____10632 =
              let uu____10638 =
                let uu____10640 = FStar_Parser_Const.const_to_string c  in
                FStar_Util.format1
                  "Ill-typed %s: this constant must be fully applied"
                  uu____10640
                 in
              (FStar_Errors.Fatal_IllTyped, uu____10638)  in
            FStar_Errors.raise_error uu____10632 r
        | uu____10644 ->
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
      | FStar_Syntax_Syntax.Total (t,uu____10663) ->
          let uu____10672 = FStar_Syntax_Util.type_u ()  in
          (match uu____10672 with
           | (k,u) ->
               let uu____10685 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10685 with
                | (t1,uu____10699,g) ->
                    let uu____10701 =
                      FStar_Syntax_Syntax.mk_Total' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10701, u, g)))
      | FStar_Syntax_Syntax.GTotal (t,uu____10703) ->
          let uu____10712 = FStar_Syntax_Util.type_u ()  in
          (match uu____10712 with
           | (k,u) ->
               let uu____10725 = tc_check_tot_or_gtot_term env t k  in
               (match uu____10725 with
                | (t1,uu____10739,g) ->
                    let uu____10741 =
                      FStar_Syntax_Syntax.mk_GTotal' t1
                        (FStar_Pervasives_Native.Some u)
                       in
                    (uu____10741, u, g)))
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
            let uu____10751 =
              let uu____10756 =
                let uu____10757 =
                  FStar_Syntax_Syntax.as_arg
                    c1.FStar_Syntax_Syntax.result_typ
                   in
                uu____10757 :: (c1.FStar_Syntax_Syntax.effect_args)  in
              FStar_Syntax_Syntax.mk_Tm_app head2 uu____10756  in
            uu____10751 FStar_Pervasives_Native.None
              (c1.FStar_Syntax_Syntax.result_typ).FStar_Syntax_Syntax.pos
             in
          let uu____10774 =
            tc_check_tot_or_gtot_term env tc FStar_Syntax_Syntax.teff  in
          (match uu____10774 with
           | (tc1,uu____10788,f) ->
               let uu____10790 = FStar_Syntax_Util.head_and_args tc1  in
               (match uu____10790 with
                | (head3,args) ->
                    let comp_univs =
                      let uu____10840 =
                        let uu____10841 = FStar_Syntax_Subst.compress head3
                           in
                        uu____10841.FStar_Syntax_Syntax.n  in
                      match uu____10840 with
                      | FStar_Syntax_Syntax.Tm_uinst (uu____10844,us) -> us
                      | uu____10850 -> []  in
                    let uu____10851 = FStar_Syntax_Util.head_and_args tc1  in
                    (match uu____10851 with
                     | (uu____10874,args1) ->
                         let uu____10900 =
                           let uu____10923 = FStar_List.hd args1  in
                           let uu____10940 = FStar_List.tl args1  in
                           (uu____10923, uu____10940)  in
                         (match uu____10900 with
                          | (res,args2) ->
                              let uu____11021 =
                                let uu____11030 =
                                  FStar_All.pipe_right
                                    c1.FStar_Syntax_Syntax.flags
                                    (FStar_List.map
                                       (fun uu___5_11058  ->
                                          match uu___5_11058 with
                                          | FStar_Syntax_Syntax.DECREASES e
                                              ->
                                              let uu____11066 =
                                                FStar_TypeChecker_Env.clear_expected_typ
                                                  env
                                                 in
                                              (match uu____11066 with
                                               | (env1,uu____11078) ->
                                                   let uu____11083 =
                                                     tc_tot_or_gtot_term env1
                                                       e
                                                      in
                                                   (match uu____11083 with
                                                    | (e1,uu____11095,g) ->
                                                        ((FStar_Syntax_Syntax.DECREASES
                                                            e1), g)))
                                          | f1 ->
                                              (f1,
                                                FStar_TypeChecker_Env.trivial_guard)))
                                   in
                                FStar_All.pipe_right uu____11030
                                  FStar_List.unzip
                                 in
                              (match uu____11021 with
                               | (flags,guards) ->
                                   let u =
                                     env.FStar_TypeChecker_Env.universe_of
                                       env (FStar_Pervasives_Native.fst res)
                                      in
                                   let c2 =
                                     FStar_Syntax_Syntax.mk_Comp
                                       (let uu___1576_11136 = c1  in
                                        {
                                          FStar_Syntax_Syntax.comp_univs =
                                            comp_univs;
                                          FStar_Syntax_Syntax.effect_name =
                                            (uu___1576_11136.FStar_Syntax_Syntax.effect_name);
                                          FStar_Syntax_Syntax.result_typ =
                                            (FStar_Pervasives_Native.fst res);
                                          FStar_Syntax_Syntax.effect_args =
                                            args2;
                                          FStar_Syntax_Syntax.flags =
                                            (uu___1576_11136.FStar_Syntax_Syntax.flags)
                                        })
                                      in
                                   let u_c =
                                     FStar_All.pipe_right c2
                                       (FStar_TypeChecker_Util.universe_of_comp
                                          env u)
                                      in
                                   let uu____11142 =
                                     FStar_List.fold_left
                                       FStar_TypeChecker_Env.conj_guard f
                                       guards
                                      in
                                   (c2, u_c, uu____11142))))))

and (tc_universe :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun u  ->
      let rec aux u1 =
        let u2 = FStar_Syntax_Subst.compress_univ u1  in
        match u2 with
        | FStar_Syntax_Syntax.U_bvar uu____11152 ->
            failwith "Impossible: locally nameless"
        | FStar_Syntax_Syntax.U_unknown  -> failwith "Unknown universe"
        | FStar_Syntax_Syntax.U_unif uu____11156 -> u2
        | FStar_Syntax_Syntax.U_zero  -> u2
        | FStar_Syntax_Syntax.U_succ u3 ->
            let uu____11166 = aux u3  in
            FStar_Syntax_Syntax.U_succ uu____11166
        | FStar_Syntax_Syntax.U_max us ->
            let uu____11170 = FStar_List.map aux us  in
            FStar_Syntax_Syntax.U_max uu____11170
        | FStar_Syntax_Syntax.U_name x ->
            let uu____11174 =
              env.FStar_TypeChecker_Env.use_bv_sorts ||
                (FStar_TypeChecker_Env.lookup_univ env x)
               in
            if uu____11174
            then u2
            else
              (let uu____11179 =
                 let uu____11181 =
                   let uu____11183 = FStar_Syntax_Print.univ_to_string u2  in
                   Prims.op_Hat uu____11183 " not found"  in
                 Prims.op_Hat "Universe variable " uu____11181  in
               failwith uu____11179)
         in
      if env.FStar_TypeChecker_Env.lax_universes
      then FStar_Syntax_Syntax.U_zero
      else
        (match u with
         | FStar_Syntax_Syntax.U_unknown  ->
             let uu____11190 = FStar_Syntax_Util.type_u ()  in
             FStar_All.pipe_right uu____11190 FStar_Pervasives_Native.snd
         | uu____11199 -> aux u)

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
            let uu____11230 =
              FStar_TypeChecker_Err.expected_a_term_of_type_t_got_a_function
                env msg t top
               in
            FStar_Errors.raise_error uu____11230 top.FStar_Syntax_Syntax.pos
             in
          let check_binders env1 bs1 bs_expected =
            let rec aux uu____11319 bs2 bs_expected1 =
              match uu____11319 with
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
                              uu____11510),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11511)) -> true
                           | (FStar_Pervasives_Native.None
                              ,FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Equality )) -> true
                           | (FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Implicit
                              uu____11526),FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Meta uu____11527)) -> true
                           | uu____11536 -> false  in
                         let uu____11546 =
                           (Prims.op_Negation (special imp imp')) &&
                             (let uu____11549 =
                                FStar_Syntax_Util.eq_aqual imp imp'  in
                              uu____11549 <> FStar_Syntax_Util.Equal)
                            in
                         if uu____11546
                         then
                           let uu____11551 =
                             let uu____11557 =
                               let uu____11559 =
                                 FStar_Syntax_Print.bv_to_string hd1  in
                               FStar_Util.format1
                                 "Inconsistent implicit argument annotation on argument %s"
                                 uu____11559
                                in
                             (FStar_Errors.Fatal_InconsistentImplicitArgumentAnnotation,
                               uu____11557)
                              in
                           let uu____11563 =
                             FStar_Syntax_Syntax.range_of_bv hd1  in
                           FStar_Errors.raise_error uu____11551 uu____11563
                         else ());
                        (let expected_t =
                           FStar_Syntax_Subst.subst subst1
                             hd_expected.FStar_Syntax_Syntax.sort
                            in
                         let uu____11567 =
                           let uu____11574 =
                             let uu____11575 =
                               FStar_Syntax_Util.unmeta
                                 hd1.FStar_Syntax_Syntax.sort
                                in
                             uu____11575.FStar_Syntax_Syntax.n  in
                           match uu____11574 with
                           | FStar_Syntax_Syntax.Tm_unknown  ->
                               (expected_t,
                                 FStar_TypeChecker_Env.trivial_guard)
                           | uu____11586 ->
                               ((let uu____11588 =
                                   FStar_TypeChecker_Env.debug env2
                                     FStar_Options.High
                                    in
                                 if uu____11588
                                 then
                                   let uu____11591 =
                                     FStar_Syntax_Print.bv_to_string hd1  in
                                   FStar_Util.print1 "Checking binder %s\n"
                                     uu____11591
                                 else ());
                                (let uu____11596 =
                                   tc_tot_or_gtot_term env2
                                     hd1.FStar_Syntax_Syntax.sort
                                    in
                                 match uu____11596 with
                                 | (t,uu____11610,g1_env) ->
                                     let g2_env =
                                       let uu____11613 =
                                         FStar_TypeChecker_Rel.teq_nosmt_force
                                           env2 t expected_t
                                          in
                                       if uu____11613
                                       then
                                         FStar_TypeChecker_Env.trivial_guard
                                       else
                                         (let uu____11618 =
                                            FStar_TypeChecker_Rel.get_subtyping_prop
                                              env2 expected_t t
                                             in
                                          match uu____11618 with
                                          | FStar_Pervasives_Native.None  ->
                                              let uu____11621 =
                                                FStar_TypeChecker_Err.basic_type_error
                                                  env2
                                                  FStar_Pervasives_Native.None
                                                  expected_t t
                                                 in
                                              let uu____11627 =
                                                FStar_TypeChecker_Env.get_range
                                                  env2
                                                 in
                                              FStar_Errors.raise_error
                                                uu____11621 uu____11627
                                          | FStar_Pervasives_Native.Some
                                              g_env ->
                                              FStar_TypeChecker_Util.label_guard
                                                (hd1.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos
                                                "Type annotation on parameter incompatible with the expected type"
                                                g_env)
                                        in
                                     let uu____11630 =
                                       FStar_TypeChecker_Env.conj_guard
                                         g1_env g2_env
                                        in
                                     (t, uu____11630)))
                            in
                         match uu____11567 with
                         | (t,g_env) ->
                             let hd2 =
                               let uu___1674_11656 = hd1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___1674_11656.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___1674_11656.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t
                               }  in
                             let b = (hd2, imp)  in
                             let b_expected = (hd_expected, imp')  in
                             let env_b = push_binding env2 b  in
                             let subst2 =
                               let uu____11679 =
                                 FStar_Syntax_Syntax.bv_to_name hd2  in
                               maybe_extend_subst subst1 b_expected
                                 uu____11679
                                in
                             let uu____11682 =
                               aux (env_b, subst2) bs3 bs_expected2  in
                             (match uu____11682 with
                              | (env_bs,bs4,rest,g'_env_b,subst3) ->
                                  let g'_env =
                                    FStar_TypeChecker_Env.close_guard env_bs
                                      [b] g'_env_b
                                     in
                                  let uu____11747 =
                                    FStar_TypeChecker_Env.conj_guard g_env
                                      g'_env
                                     in
                                  (env_bs, (b :: bs4), rest, uu____11747,
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
                  | uu____11919 ->
                      failwith
                        "Impossible: Can't have a let rec annotation but no expected type");
                 (let uu____11929 = tc_binders env1 bs  in
                  match uu____11929 with
                  | (bs1,envbody,g_env,uu____11959) ->
                      (FStar_Pervasives_Native.None, bs1, [],
                        FStar_Pervasives_Native.None, envbody, body1, g_env)))
            | FStar_Pervasives_Native.Some t ->
                let t1 = FStar_Syntax_Subst.compress t  in
                let rec as_function_typ norm1 t2 =
                  let uu____12015 =
                    let uu____12016 = FStar_Syntax_Subst.compress t2  in
                    uu____12016.FStar_Syntax_Syntax.n  in
                  match uu____12015 with
                  | FStar_Syntax_Syntax.Tm_uvar uu____12049 ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____12069 -> failwith "Impossible");
                       (let uu____12079 = tc_binders env1 bs  in
                        match uu____12079 with
                        | (bs1,envbody,g_env,uu____12121) ->
                            let uu____12122 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12122 with
                             | (envbody1,uu____12160) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                           uu____12181;
                         FStar_Syntax_Syntax.pos = uu____12182;
                         FStar_Syntax_Syntax.vars = uu____12183;_},uu____12184)
                      ->
                      ((match env1.FStar_TypeChecker_Env.letrecs with
                        | [] -> ()
                        | uu____12228 -> failwith "Impossible");
                       (let uu____12238 = tc_binders env1 bs  in
                        match uu____12238 with
                        | (bs1,envbody,g_env,uu____12280) ->
                            let uu____12281 =
                              FStar_TypeChecker_Env.clear_expected_typ
                                envbody
                               in
                            (match uu____12281 with
                             | (envbody1,uu____12319) ->
                                 ((FStar_Pervasives_Native.Some t2), bs1, [],
                                   FStar_Pervasives_Native.None, envbody1,
                                   body1, g_env))))
                  | FStar_Syntax_Syntax.Tm_refine (b,uu____12341) ->
                      let uu____12346 =
                        as_function_typ norm1 b.FStar_Syntax_Syntax.sort  in
                      (match uu____12346 with
                       | (uu____12407,bs1,bs',copt,env_body,body2,g_env) ->
                           ((FStar_Pervasives_Native.Some t2), bs1, bs',
                             copt, env_body, body2, g_env))
                  | FStar_Syntax_Syntax.Tm_arrow (bs_expected,c_expected) ->
                      let uu____12484 =
                        FStar_Syntax_Subst.open_comp bs_expected c_expected
                         in
                      (match uu____12484 with
                       | (bs_expected1,c_expected1) ->
                           let check_actuals_against_formals env2 bs1
                             bs_expected2 body2 =
                             let rec handle_more uu____12629 c_expected2
                               body3 =
                               match uu____12629 with
                               | (env_bs,bs2,more,guard_env,subst1) ->
                                   (match more with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____12743 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        (env_bs, bs2, guard_env, uu____12743,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inr more_bs_expected) ->
                                        let c =
                                          let uu____12760 =
                                            FStar_Syntax_Util.arrow
                                              more_bs_expected c_expected2
                                             in
                                          FStar_Syntax_Syntax.mk_Total
                                            uu____12760
                                           in
                                        let uu____12761 =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c
                                           in
                                        (env_bs, bs2, guard_env, uu____12761,
                                          body3)
                                    | FStar_Pervasives_Native.Some
                                        (FStar_Util.Inl more_bs) ->
                                        let c =
                                          FStar_Syntax_Subst.subst_comp
                                            subst1 c_expected2
                                           in
                                        let uu____12778 =
                                          (FStar_Options.ml_ish ()) ||
                                            (FStar_Syntax_Util.is_named_tot c)
                                           in
                                        if uu____12778
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
                                               let uu____12844 =
                                                 FStar_Syntax_Subst.open_comp
                                                   bs_expected3 c_expected3
                                                  in
                                               (match uu____12844 with
                                                | (bs_expected4,c_expected4)
                                                    ->
                                                    let uu____12871 =
                                                      check_binders env_bs
                                                        more_bs bs_expected4
                                                       in
                                                    (match uu____12871 with
                                                     | (env_bs_bs',bs',more1,guard'_env_bs,subst2)
                                                         ->
                                                         let guard'_env =
                                                           FStar_TypeChecker_Env.close_guard
                                                             env_bs bs2
                                                             guard'_env_bs
                                                            in
                                                         let uu____12926 =
                                                           let uu____12953 =
                                                             FStar_TypeChecker_Env.conj_guard
                                                               guard_env
                                                               guard'_env
                                                              in
                                                           (env_bs_bs',
                                                             (FStar_List.append
                                                                bs2 bs'),
                                                             more1,
                                                             uu____12953,
                                                             subst2)
                                                            in
                                                         handle_more
                                                           uu____12926
                                                           c_expected4 body3))
                                           | uu____12976 ->
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
                             let uu____13005 =
                               check_binders env2 bs1 bs_expected2  in
                             handle_more uu____13005 c_expected1 body2  in
                           let mk_letrec_env envbody bs1 c =
                             let letrecs = guard_letrecs envbody bs1 c  in
                             let envbody1 =
                               let uu___1800_13070 = envbody  in
                               {
                                 FStar_TypeChecker_Env.solver =
                                   (uu___1800_13070.FStar_TypeChecker_Env.solver);
                                 FStar_TypeChecker_Env.range =
                                   (uu___1800_13070.FStar_TypeChecker_Env.range);
                                 FStar_TypeChecker_Env.curmodule =
                                   (uu___1800_13070.FStar_TypeChecker_Env.curmodule);
                                 FStar_TypeChecker_Env.gamma =
                                   (uu___1800_13070.FStar_TypeChecker_Env.gamma);
                                 FStar_TypeChecker_Env.gamma_sig =
                                   (uu___1800_13070.FStar_TypeChecker_Env.gamma_sig);
                                 FStar_TypeChecker_Env.gamma_cache =
                                   (uu___1800_13070.FStar_TypeChecker_Env.gamma_cache);
                                 FStar_TypeChecker_Env.modules =
                                   (uu___1800_13070.FStar_TypeChecker_Env.modules);
                                 FStar_TypeChecker_Env.expected_typ =
                                   (uu___1800_13070.FStar_TypeChecker_Env.expected_typ);
                                 FStar_TypeChecker_Env.sigtab =
                                   (uu___1800_13070.FStar_TypeChecker_Env.sigtab);
                                 FStar_TypeChecker_Env.attrtab =
                                   (uu___1800_13070.FStar_TypeChecker_Env.attrtab);
                                 FStar_TypeChecker_Env.is_pattern =
                                   (uu___1800_13070.FStar_TypeChecker_Env.is_pattern);
                                 FStar_TypeChecker_Env.instantiate_imp =
                                   (uu___1800_13070.FStar_TypeChecker_Env.instantiate_imp);
                                 FStar_TypeChecker_Env.effects =
                                   (uu___1800_13070.FStar_TypeChecker_Env.effects);
                                 FStar_TypeChecker_Env.generalize =
                                   (uu___1800_13070.FStar_TypeChecker_Env.generalize);
                                 FStar_TypeChecker_Env.letrecs = [];
                                 FStar_TypeChecker_Env.top_level =
                                   (uu___1800_13070.FStar_TypeChecker_Env.top_level);
                                 FStar_TypeChecker_Env.check_uvars =
                                   (uu___1800_13070.FStar_TypeChecker_Env.check_uvars);
                                 FStar_TypeChecker_Env.use_eq =
                                   (uu___1800_13070.FStar_TypeChecker_Env.use_eq);
                                 FStar_TypeChecker_Env.is_iface =
                                   (uu___1800_13070.FStar_TypeChecker_Env.is_iface);
                                 FStar_TypeChecker_Env.admit =
                                   (uu___1800_13070.FStar_TypeChecker_Env.admit);
                                 FStar_TypeChecker_Env.lax =
                                   (uu___1800_13070.FStar_TypeChecker_Env.lax);
                                 FStar_TypeChecker_Env.lax_universes =
                                   (uu___1800_13070.FStar_TypeChecker_Env.lax_universes);
                                 FStar_TypeChecker_Env.phase1 =
                                   (uu___1800_13070.FStar_TypeChecker_Env.phase1);
                                 FStar_TypeChecker_Env.failhard =
                                   (uu___1800_13070.FStar_TypeChecker_Env.failhard);
                                 FStar_TypeChecker_Env.nosynth =
                                   (uu___1800_13070.FStar_TypeChecker_Env.nosynth);
                                 FStar_TypeChecker_Env.uvar_subtyping =
                                   (uu___1800_13070.FStar_TypeChecker_Env.uvar_subtyping);
                                 FStar_TypeChecker_Env.tc_term =
                                   (uu___1800_13070.FStar_TypeChecker_Env.tc_term);
                                 FStar_TypeChecker_Env.type_of =
                                   (uu___1800_13070.FStar_TypeChecker_Env.type_of);
                                 FStar_TypeChecker_Env.universe_of =
                                   (uu___1800_13070.FStar_TypeChecker_Env.universe_of);
                                 FStar_TypeChecker_Env.check_type_of =
                                   (uu___1800_13070.FStar_TypeChecker_Env.check_type_of);
                                 FStar_TypeChecker_Env.use_bv_sorts =
                                   (uu___1800_13070.FStar_TypeChecker_Env.use_bv_sorts);
                                 FStar_TypeChecker_Env.qtbl_name_and_index =
                                   (uu___1800_13070.FStar_TypeChecker_Env.qtbl_name_and_index);
                                 FStar_TypeChecker_Env.normalized_eff_names =
                                   (uu___1800_13070.FStar_TypeChecker_Env.normalized_eff_names);
                                 FStar_TypeChecker_Env.fv_delta_depths =
                                   (uu___1800_13070.FStar_TypeChecker_Env.fv_delta_depths);
                                 FStar_TypeChecker_Env.proof_ns =
                                   (uu___1800_13070.FStar_TypeChecker_Env.proof_ns);
                                 FStar_TypeChecker_Env.synth_hook =
                                   (uu___1800_13070.FStar_TypeChecker_Env.synth_hook);
                                 FStar_TypeChecker_Env.try_solve_implicits_hook
                                   =
                                   (uu___1800_13070.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                 FStar_TypeChecker_Env.splice =
                                   (uu___1800_13070.FStar_TypeChecker_Env.splice);
                                 FStar_TypeChecker_Env.postprocess =
                                   (uu___1800_13070.FStar_TypeChecker_Env.postprocess);
                                 FStar_TypeChecker_Env.is_native_tactic =
                                   (uu___1800_13070.FStar_TypeChecker_Env.is_native_tactic);
                                 FStar_TypeChecker_Env.identifier_info =
                                   (uu___1800_13070.FStar_TypeChecker_Env.identifier_info);
                                 FStar_TypeChecker_Env.tc_hooks =
                                   (uu___1800_13070.FStar_TypeChecker_Env.tc_hooks);
                                 FStar_TypeChecker_Env.dsenv =
                                   (uu___1800_13070.FStar_TypeChecker_Env.dsenv);
                                 FStar_TypeChecker_Env.nbe =
                                   (uu___1800_13070.FStar_TypeChecker_Env.nbe);
                                 FStar_TypeChecker_Env.strict_args_tab =
                                   (uu___1800_13070.FStar_TypeChecker_Env.strict_args_tab);
                                 FStar_TypeChecker_Env.erasable_types_tab =
                                   (uu___1800_13070.FStar_TypeChecker_Env.erasable_types_tab)
                               }  in
                             let uu____13077 =
                               FStar_All.pipe_right letrecs
                                 (FStar_List.fold_left
                                    (fun uu____13143  ->
                                       fun uu____13144  ->
                                         match (uu____13143, uu____13144)
                                         with
                                         | ((env2,letrec_binders,g),(l,t3,u_names))
                                             ->
                                             let uu____13235 =
                                               let uu____13242 =
                                                 let uu____13243 =
                                                   FStar_TypeChecker_Env.clear_expected_typ
                                                     env2
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____13243
                                                   FStar_Pervasives_Native.fst
                                                  in
                                               tc_term uu____13242 t3  in
                                             (match uu____13235 with
                                              | (t4,uu____13267,g') ->
                                                  let env3 =
                                                    FStar_TypeChecker_Env.push_let_binding
                                                      env2 l (u_names, t4)
                                                     in
                                                  let lb =
                                                    match l with
                                                    | FStar_Util.Inl x ->
                                                        let uu____13280 =
                                                          FStar_Syntax_Syntax.mk_binder
                                                            (let uu___1818_13283
                                                               = x  in
                                                             {
                                                               FStar_Syntax_Syntax.ppname
                                                                 =
                                                                 (uu___1818_13283.FStar_Syntax_Syntax.ppname);
                                                               FStar_Syntax_Syntax.index
                                                                 =
                                                                 (uu___1818_13283.FStar_Syntax_Syntax.index);
                                                               FStar_Syntax_Syntax.sort
                                                                 = t4
                                                             })
                                                           in
                                                        uu____13280 ::
                                                          letrec_binders
                                                    | uu____13284 ->
                                                        letrec_binders
                                                     in
                                                  let uu____13289 =
                                                    FStar_TypeChecker_Env.conj_guard
                                                      g g'
                                                     in
                                                  (env3, lb, uu____13289)))
                                    (envbody1, [],
                                      FStar_TypeChecker_Env.trivial_guard))
                                in
                             match uu____13077 with
                             | (envbody2,letrec_binders,g) ->
                                 let uu____13309 =
                                   FStar_TypeChecker_Env.close_guard envbody2
                                     bs1 g
                                    in
                                 (envbody2, letrec_binders, uu____13309)
                              in
                           let uu____13312 =
                             check_actuals_against_formals env1 bs
                               bs_expected1 body1
                              in
                           (match uu____13312 with
                            | (envbody,bs1,g_env,c,body2) ->
                                let uu____13388 = mk_letrec_env envbody bs1 c
                                   in
                                (match uu____13388 with
                                 | (envbody1,letrecs,g_annots) ->
                                     let envbody2 =
                                       FStar_TypeChecker_Env.set_expected_typ
                                         envbody1
                                         (FStar_Syntax_Util.comp_result c)
                                        in
                                     let uu____13435 =
                                       FStar_TypeChecker_Env.conj_guard g_env
                                         g_annots
                                        in
                                     ((FStar_Pervasives_Native.Some t2), bs1,
                                       letrecs,
                                       (FStar_Pervasives_Native.Some c),
                                       envbody2, body2, uu____13435))))
                  | uu____13452 ->
                      if Prims.op_Negation norm1
                      then
                        let uu____13484 =
                          let uu____13485 =
                            FStar_All.pipe_right t2
                              (FStar_TypeChecker_Normalize.unfold_whnf env1)
                             in
                          FStar_All.pipe_right uu____13485
                            FStar_Syntax_Util.unascribe
                           in
                        as_function_typ true uu____13484
                      else
                        (let uu____13489 =
                           expected_function_typ1 env1
                             FStar_Pervasives_Native.None body1
                            in
                         match uu____13489 with
                         | (uu____13538,bs1,uu____13540,c_opt,envbody,body2,g_env)
                             ->
                             ((FStar_Pervasives_Native.Some t2), bs1, [],
                               c_opt, envbody, body2, g_env))
                   in
                as_function_typ false t1
             in
          let use_eq = env.FStar_TypeChecker_Env.use_eq  in
          let uu____13572 = FStar_TypeChecker_Env.clear_expected_typ env  in
          match uu____13572 with
          | (env1,topt) ->
              ((let uu____13592 =
                  FStar_TypeChecker_Env.debug env1 FStar_Options.High  in
                if uu____13592
                then
                  let uu____13595 =
                    match topt with
                    | FStar_Pervasives_Native.None  -> "None"
                    | FStar_Pervasives_Native.Some t ->
                        FStar_Syntax_Print.term_to_string t
                     in
                  FStar_Util.print2
                    "!!!!!!!!!!!!!!!Expected type is %s, top_level=%s\n"
                    uu____13595
                    (if env1.FStar_TypeChecker_Env.top_level
                     then "true"
                     else "false")
                else ());
               (let uu____13609 = expected_function_typ1 env1 topt body  in
                match uu____13609 with
                | (tfun_opt,bs1,letrec_binders,c_opt,envbody,body1,g_env) ->
                    ((let uu____13650 =
                        FStar_TypeChecker_Env.debug env1
                          FStar_Options.Extreme
                         in
                      if uu____13650
                      then
                        let uu____13653 =
                          match tfun_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        let uu____13658 =
                          match c_opt with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.comp_to_string t
                           in
                        let uu____13663 =
                          let uu____13665 =
                            FStar_TypeChecker_Env.expected_typ envbody  in
                          match uu____13665 with
                          | FStar_Pervasives_Native.None  -> "None"
                          | FStar_Pervasives_Native.Some t ->
                              FStar_Syntax_Print.term_to_string t
                           in
                        FStar_Util.print3
                          "After expected_function_typ, tfun_opt: %s, c_opt: %s, and expected type in envbody: %s\n"
                          uu____13653 uu____13658 uu____13663
                      else ());
                     (let uu____13675 =
                        FStar_All.pipe_left
                          (FStar_TypeChecker_Env.debug env1)
                          (FStar_Options.Other "NYC")
                         in
                      if uu____13675
                      then
                        let uu____13680 =
                          FStar_Syntax_Print.binders_to_string ", " bs1  in
                        let uu____13683 =
                          FStar_TypeChecker_Rel.guard_to_string env1 g_env
                           in
                        FStar_Util.print2
                          "!!!!!!!!!!!!!!!Guard for function with binders %s is %s\n"
                          uu____13680 uu____13683
                      else ());
                     (let envbody1 =
                        FStar_TypeChecker_Env.set_range envbody
                          body1.FStar_Syntax_Syntax.pos
                         in
                      let uu____13689 =
                        let should_check_expected_effect =
                          let uu____13702 =
                            let uu____13709 =
                              let uu____13710 =
                                FStar_Syntax_Subst.compress body1  in
                              uu____13710.FStar_Syntax_Syntax.n  in
                            (c_opt, uu____13709)  in
                          match uu____13702 with
                          | (FStar_Pervasives_Native.None
                             ,FStar_Syntax_Syntax.Tm_ascribed
                             (uu____13716,(FStar_Util.Inr
                                           expected_c,uu____13718),uu____13719))
                              -> false
                          | uu____13769 -> true  in
                        let uu____13777 =
                          tc_term
                            (let uu___1891_13786 = envbody1  in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___1891_13786.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___1891_13786.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___1891_13786.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___1891_13786.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_sig =
                                 (uu___1891_13786.FStar_TypeChecker_Env.gamma_sig);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___1891_13786.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___1891_13786.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___1891_13786.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___1891_13786.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.attrtab =
                                 (uu___1891_13786.FStar_TypeChecker_Env.attrtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___1891_13786.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___1891_13786.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___1891_13786.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___1891_13786.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___1891_13786.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level = false;
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___1891_13786.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq = use_eq;
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___1891_13786.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___1891_13786.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax =
                                 (uu___1891_13786.FStar_TypeChecker_Env.lax);
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___1891_13786.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.phase1 =
                                 (uu___1891_13786.FStar_TypeChecker_Env.phase1);
                               FStar_TypeChecker_Env.failhard =
                                 (uu___1891_13786.FStar_TypeChecker_Env.failhard);
                               FStar_TypeChecker_Env.nosynth =
                                 (uu___1891_13786.FStar_TypeChecker_Env.nosynth);
                               FStar_TypeChecker_Env.uvar_subtyping =
                                 (uu___1891_13786.FStar_TypeChecker_Env.uvar_subtyping);
                               FStar_TypeChecker_Env.tc_term =
                                 (uu___1891_13786.FStar_TypeChecker_Env.tc_term);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___1891_13786.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___1891_13786.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.check_type_of =
                                 (uu___1891_13786.FStar_TypeChecker_Env.check_type_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___1891_13786.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qtbl_name_and_index =
                                 (uu___1891_13786.FStar_TypeChecker_Env.qtbl_name_and_index);
                               FStar_TypeChecker_Env.normalized_eff_names =
                                 (uu___1891_13786.FStar_TypeChecker_Env.normalized_eff_names);
                               FStar_TypeChecker_Env.fv_delta_depths =
                                 (uu___1891_13786.FStar_TypeChecker_Env.fv_delta_depths);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___1891_13786.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth_hook =
                                 (uu___1891_13786.FStar_TypeChecker_Env.synth_hook);
                               FStar_TypeChecker_Env.try_solve_implicits_hook
                                 =
                                 (uu___1891_13786.FStar_TypeChecker_Env.try_solve_implicits_hook);
                               FStar_TypeChecker_Env.splice =
                                 (uu___1891_13786.FStar_TypeChecker_Env.splice);
                               FStar_TypeChecker_Env.postprocess =
                                 (uu___1891_13786.FStar_TypeChecker_Env.postprocess);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___1891_13786.FStar_TypeChecker_Env.is_native_tactic);
                               FStar_TypeChecker_Env.identifier_info =
                                 (uu___1891_13786.FStar_TypeChecker_Env.identifier_info);
                               FStar_TypeChecker_Env.tc_hooks =
                                 (uu___1891_13786.FStar_TypeChecker_Env.tc_hooks);
                               FStar_TypeChecker_Env.dsenv =
                                 (uu___1891_13786.FStar_TypeChecker_Env.dsenv);
                               FStar_TypeChecker_Env.nbe =
                                 (uu___1891_13786.FStar_TypeChecker_Env.nbe);
                               FStar_TypeChecker_Env.strict_args_tab =
                                 (uu___1891_13786.FStar_TypeChecker_Env.strict_args_tab);
                               FStar_TypeChecker_Env.erasable_types_tab =
                                 (uu___1891_13786.FStar_TypeChecker_Env.erasable_types_tab)
                             }) body1
                           in
                        match uu____13777 with
                        | (body2,cbody,guard_body) ->
                            let guard_body1 =
                              FStar_TypeChecker_Rel.solve_deferred_constraints
                                envbody1 guard_body
                               in
                            if should_check_expected_effect
                            then
                              let uu____13813 =
                                FStar_TypeChecker_Common.lcomp_comp cbody  in
                              (match uu____13813 with
                               | (cbody1,g_lc) ->
                                   let uu____13830 =
                                     check_expected_effect
                                       (let uu___1902_13839 = envbody1  in
                                        {
                                          FStar_TypeChecker_Env.solver =
                                            (uu___1902_13839.FStar_TypeChecker_Env.solver);
                                          FStar_TypeChecker_Env.range =
                                            (uu___1902_13839.FStar_TypeChecker_Env.range);
                                          FStar_TypeChecker_Env.curmodule =
                                            (uu___1902_13839.FStar_TypeChecker_Env.curmodule);
                                          FStar_TypeChecker_Env.gamma =
                                            (uu___1902_13839.FStar_TypeChecker_Env.gamma);
                                          FStar_TypeChecker_Env.gamma_sig =
                                            (uu___1902_13839.FStar_TypeChecker_Env.gamma_sig);
                                          FStar_TypeChecker_Env.gamma_cache =
                                            (uu___1902_13839.FStar_TypeChecker_Env.gamma_cache);
                                          FStar_TypeChecker_Env.modules =
                                            (uu___1902_13839.FStar_TypeChecker_Env.modules);
                                          FStar_TypeChecker_Env.expected_typ
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.expected_typ);
                                          FStar_TypeChecker_Env.sigtab =
                                            (uu___1902_13839.FStar_TypeChecker_Env.sigtab);
                                          FStar_TypeChecker_Env.attrtab =
                                            (uu___1902_13839.FStar_TypeChecker_Env.attrtab);
                                          FStar_TypeChecker_Env.is_pattern =
                                            (uu___1902_13839.FStar_TypeChecker_Env.is_pattern);
                                          FStar_TypeChecker_Env.instantiate_imp
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.instantiate_imp);
                                          FStar_TypeChecker_Env.effects =
                                            (uu___1902_13839.FStar_TypeChecker_Env.effects);
                                          FStar_TypeChecker_Env.generalize =
                                            (uu___1902_13839.FStar_TypeChecker_Env.generalize);
                                          FStar_TypeChecker_Env.letrecs =
                                            (uu___1902_13839.FStar_TypeChecker_Env.letrecs);
                                          FStar_TypeChecker_Env.top_level =
                                            (uu___1902_13839.FStar_TypeChecker_Env.top_level);
                                          FStar_TypeChecker_Env.check_uvars =
                                            (uu___1902_13839.FStar_TypeChecker_Env.check_uvars);
                                          FStar_TypeChecker_Env.use_eq =
                                            use_eq;
                                          FStar_TypeChecker_Env.is_iface =
                                            (uu___1902_13839.FStar_TypeChecker_Env.is_iface);
                                          FStar_TypeChecker_Env.admit =
                                            (uu___1902_13839.FStar_TypeChecker_Env.admit);
                                          FStar_TypeChecker_Env.lax =
                                            (uu___1902_13839.FStar_TypeChecker_Env.lax);
                                          FStar_TypeChecker_Env.lax_universes
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.lax_universes);
                                          FStar_TypeChecker_Env.phase1 =
                                            (uu___1902_13839.FStar_TypeChecker_Env.phase1);
                                          FStar_TypeChecker_Env.failhard =
                                            (uu___1902_13839.FStar_TypeChecker_Env.failhard);
                                          FStar_TypeChecker_Env.nosynth =
                                            (uu___1902_13839.FStar_TypeChecker_Env.nosynth);
                                          FStar_TypeChecker_Env.uvar_subtyping
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.uvar_subtyping);
                                          FStar_TypeChecker_Env.tc_term =
                                            (uu___1902_13839.FStar_TypeChecker_Env.tc_term);
                                          FStar_TypeChecker_Env.type_of =
                                            (uu___1902_13839.FStar_TypeChecker_Env.type_of);
                                          FStar_TypeChecker_Env.universe_of =
                                            (uu___1902_13839.FStar_TypeChecker_Env.universe_of);
                                          FStar_TypeChecker_Env.check_type_of
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.check_type_of);
                                          FStar_TypeChecker_Env.use_bv_sorts
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.use_bv_sorts);
                                          FStar_TypeChecker_Env.qtbl_name_and_index
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.qtbl_name_and_index);
                                          FStar_TypeChecker_Env.normalized_eff_names
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.normalized_eff_names);
                                          FStar_TypeChecker_Env.fv_delta_depths
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.fv_delta_depths);
                                          FStar_TypeChecker_Env.proof_ns =
                                            (uu___1902_13839.FStar_TypeChecker_Env.proof_ns);
                                          FStar_TypeChecker_Env.synth_hook =
                                            (uu___1902_13839.FStar_TypeChecker_Env.synth_hook);
                                          FStar_TypeChecker_Env.try_solve_implicits_hook
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                          FStar_TypeChecker_Env.splice =
                                            (uu___1902_13839.FStar_TypeChecker_Env.splice);
                                          FStar_TypeChecker_Env.postprocess =
                                            (uu___1902_13839.FStar_TypeChecker_Env.postprocess);
                                          FStar_TypeChecker_Env.is_native_tactic
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.is_native_tactic);
                                          FStar_TypeChecker_Env.identifier_info
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.identifier_info);
                                          FStar_TypeChecker_Env.tc_hooks =
                                            (uu___1902_13839.FStar_TypeChecker_Env.tc_hooks);
                                          FStar_TypeChecker_Env.dsenv =
                                            (uu___1902_13839.FStar_TypeChecker_Env.dsenv);
                                          FStar_TypeChecker_Env.nbe =
                                            (uu___1902_13839.FStar_TypeChecker_Env.nbe);
                                          FStar_TypeChecker_Env.strict_args_tab
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.strict_args_tab);
                                          FStar_TypeChecker_Env.erasable_types_tab
                                            =
                                            (uu___1902_13839.FStar_TypeChecker_Env.erasable_types_tab)
                                        }) c_opt (body2, cbody1)
                                      in
                                   (match uu____13830 with
                                    | (body3,cbody2,guard) ->
                                        let uu____13853 =
                                          let uu____13854 =
                                            FStar_TypeChecker_Env.conj_guard
                                              g_lc guard
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            guard_body1 uu____13854
                                           in
                                        (body3, cbody2, uu____13853)))
                            else
                              (let uu____13861 =
                                 FStar_TypeChecker_Common.lcomp_comp cbody
                                  in
                               match uu____13861 with
                               | (cbody1,g_lc) ->
                                   let uu____13878 =
                                     FStar_TypeChecker_Env.conj_guard
                                       guard_body1 g_lc
                                      in
                                   (body2, cbody1, uu____13878))
                         in
                      match uu____13689 with
                      | (body2,cbody,guard_body) ->
                          let guard =
                            let uu____13901 =
                              env1.FStar_TypeChecker_Env.top_level ||
                                (let uu____13904 =
                                   FStar_TypeChecker_Env.should_verify env1
                                    in
                                 Prims.op_Negation uu____13904)
                               in
                            if uu____13901
                            then
                              let uu____13907 =
                                FStar_TypeChecker_Rel.discharge_guard env1
                                  g_env
                                 in
                              let uu____13908 =
                                FStar_TypeChecker_Rel.discharge_guard
                                  envbody1 guard_body
                                 in
                              FStar_TypeChecker_Env.conj_guard uu____13907
                                uu____13908
                            else
                              (let guard =
                                 let uu____13912 =
                                   FStar_TypeChecker_Env.close_guard env1
                                     (FStar_List.append bs1 letrec_binders)
                                     guard_body
                                    in
                                 FStar_TypeChecker_Env.conj_guard g_env
                                   uu____13912
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
                          let uu____13926 =
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
                                 | FStar_Syntax_Syntax.Tm_arrow uu____13950
                                     -> (e, t_annot, guard1)
                                 | uu____13965 ->
                                     let uu____13966 =
                                       FStar_TypeChecker_Util.check_and_ascribe
                                         env1 e tfun_computed t1
                                        in
                                     (match uu____13966 with
                                      | (e1,guard') ->
                                          let uu____13979 =
                                            FStar_TypeChecker_Env.conj_guard
                                              guard1 guard'
                                             in
                                          (e1, t_annot, uu____13979)))
                            | FStar_Pervasives_Native.None  ->
                                (e, tfun_computed, guard1)
                             in
                          (match uu____13926 with
                           | (e1,tfun,guard2) ->
                               let c = FStar_Syntax_Syntax.mk_Total tfun  in
                               let uu____13990 =
                                 let uu____13995 =
                                   FStar_TypeChecker_Common.lcomp_of_comp c
                                    in
                                 FStar_TypeChecker_Util.strengthen_precondition
                                   FStar_Pervasives_Native.None env1 e1
                                   uu____13995 guard2
                                  in
                               (match uu____13990 with
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
              (let uu____14046 =
                 FStar_TypeChecker_Env.debug env FStar_Options.High  in
               if uu____14046
               then
                 let uu____14049 =
                   FStar_Range.string_of_range head1.FStar_Syntax_Syntax.pos
                    in
                 let uu____14051 = FStar_Syntax_Print.term_to_string thead
                    in
                 FStar_Util.print2 "(%s) Type of head is %s\n" uu____14049
                   uu____14051
               else ());
              (let monadic_application uu____14133 subst1 arg_comps_rev
                 arg_rets_rev guard fvs bs =
                 match uu____14133 with
                 | (head2,chead1,ghead1,cres) ->
                     let uu____14202 =
                       check_no_escape (FStar_Pervasives_Native.Some head2)
                         env fvs (FStar_Syntax_Util.comp_result cres)
                        in
                     (match uu____14202 with
                      | (rt,g0) ->
                          let cres1 =
                            FStar_Syntax_Util.set_result_typ cres rt  in
                          let uu____14216 =
                            match bs with
                            | [] ->
                                let g =
                                  let uu____14232 =
                                    FStar_TypeChecker_Env.conj_guard ghead1
                                      guard
                                     in
                                  FStar_All.pipe_left
                                    (FStar_TypeChecker_Env.conj_guard g0)
                                    uu____14232
                                   in
                                (cres1, g)
                            | uu____14233 ->
                                let g =
                                  let uu____14243 =
                                    let uu____14244 =
                                      FStar_TypeChecker_Env.conj_guard ghead1
                                        guard
                                       in
                                    FStar_All.pipe_right uu____14244
                                      (FStar_TypeChecker_Rel.solve_deferred_constraints
                                         env)
                                     in
                                  FStar_TypeChecker_Env.conj_guard g0
                                    uu____14243
                                   in
                                let uu____14245 =
                                  let uu____14246 =
                                    FStar_Syntax_Util.arrow bs cres1  in
                                  FStar_Syntax_Syntax.mk_Total uu____14246
                                   in
                                (uu____14245, g)
                             in
                          (match uu____14216 with
                           | (cres2,guard1) ->
                               ((let uu____14256 =
                                   FStar_TypeChecker_Env.debug env
                                     FStar_Options.Low
                                    in
                                 if uu____14256
                                 then
                                   let uu____14259 =
                                     FStar_Syntax_Print.comp_to_string cres2
                                      in
                                   FStar_Util.print1
                                     "\t Type of result cres is %s\n"
                                     uu____14259
                                 else ());
                                (let uu____14264 =
                                   let uu____14269 =
                                     let uu____14270 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         chead1
                                        in
                                     FStar_All.pipe_right uu____14270
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   let uu____14271 =
                                     let uu____14272 =
                                       FStar_Syntax_Subst.subst_comp subst1
                                         cres2
                                        in
                                     FStar_All.pipe_right uu____14272
                                       FStar_TypeChecker_Common.lcomp_of_comp
                                      in
                                   (uu____14269, uu____14271)  in
                                 match uu____14264 with
                                 | (chead2,cres3) ->
                                     let cres4 =
                                       let head_is_pure_and_some_arg_is_effectful
                                         =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2)
                                           &&
                                           (FStar_Util.for_some
                                              (fun uu____14296  ->
                                                 match uu____14296 with
                                                 | (uu____14306,uu____14307,lc)
                                                     ->
                                                     (let uu____14315 =
                                                        FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                          lc
                                                         in
                                                      Prims.op_Negation
                                                        uu____14315)
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
                                       let uu____14328 =
                                         (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            cres3)
                                           &&
                                           head_is_pure_and_some_arg_is_effectful
                                          in
                                       if uu____14328
                                       then
                                         ((let uu____14332 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____14332
                                           then
                                             let uu____14335 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: Return inserted in monadic application: %s\n"
                                               uu____14335
                                           else ());
                                          FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                            env term cres3)
                                       else
                                         ((let uu____14343 =
                                             FStar_TypeChecker_Env.debug env
                                               FStar_Options.Extreme
                                              in
                                           if uu____14343
                                           then
                                             let uu____14346 =
                                               FStar_Syntax_Print.term_to_string
                                                 term
                                                in
                                             FStar_Util.print1
                                               "(a) Monadic app: No return inserted in monadic application: %s\n"
                                               uu____14346
                                           else ());
                                          cres3)
                                        in
                                     let comp =
                                       FStar_List.fold_left
                                         (fun out_c  ->
                                            fun uu____14377  ->
                                              match uu____14377 with
                                              | ((e,q),x,c) ->
                                                  ((let uu____14419 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14419
                                                    then
                                                      let uu____14422 =
                                                        match x with
                                                        | FStar_Pervasives_Native.None
                                                             -> "_"
                                                        | FStar_Pervasives_Native.Some
                                                            x1 ->
                                                            FStar_Syntax_Print.bv_to_string
                                                              x1
                                                         in
                                                      let uu____14427 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____14429 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print3
                                                        "(b) Monadic app: Binding argument %s : %s of type (%s)\n"
                                                        uu____14422
                                                        uu____14427
                                                        uu____14429
                                                    else ());
                                                   (let uu____14434 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____14434
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
                                       (let uu____14445 =
                                          FStar_TypeChecker_Env.debug env
                                            FStar_Options.Extreme
                                           in
                                        if uu____14445
                                        then
                                          let uu____14448 =
                                            FStar_Syntax_Print.term_to_string
                                              head2
                                             in
                                          FStar_Util.print1
                                            "(c) Monadic app: Binding head %s\n"
                                            uu____14448
                                        else ());
                                       (let uu____14453 =
                                          FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                            chead2
                                           in
                                        if uu____14453
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
                                       let uu____14464 =
                                         let uu____14465 =
                                           FStar_Syntax_Subst.compress head2
                                            in
                                         uu____14465.FStar_Syntax_Syntax.n
                                          in
                                       match uu____14464 with
                                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                                           (FStar_Syntax_Syntax.fv_eq_lid fv
                                              FStar_Parser_Const.op_And)
                                             ||
                                             (FStar_Syntax_Syntax.fv_eq_lid
                                                fv FStar_Parser_Const.op_Or)
                                       | uu____14470 -> false  in
                                     let app =
                                       if shortcuts_evaluation_order
                                       then
                                         let args1 =
                                           FStar_List.fold_left
                                             (fun args1  ->
                                                fun uu____14493  ->
                                                  match uu____14493 with
                                                  | (arg,uu____14507,uu____14508)
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
                                         (let uu____14519 =
                                            let map_fun uu____14585 =
                                              match uu____14585 with
                                              | ((e,q),uu____14626,c) ->
                                                  ((let uu____14649 =
                                                      FStar_TypeChecker_Env.debug
                                                        env
                                                        FStar_Options.Extreme
                                                       in
                                                    if uu____14649
                                                    then
                                                      let uu____14652 =
                                                        FStar_Syntax_Print.term_to_string
                                                          e
                                                         in
                                                      let uu____14654 =
                                                        FStar_TypeChecker_Common.lcomp_to_string
                                                          c
                                                         in
                                                      FStar_Util.print2
                                                        "For arg e=(%s) c=(%s)... "
                                                        uu____14652
                                                        uu____14654
                                                    else ());
                                                   (let uu____14659 =
                                                      FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                        c
                                                       in
                                                    if uu____14659
                                                    then
                                                      ((let uu____14685 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____14685
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
                                                           (let uu____14726 =
                                                              let uu____14728
                                                                =
                                                                let uu____14729
                                                                  =
                                                                  FStar_Syntax_Util.un_uinst
                                                                    head2
                                                                   in
                                                                uu____14729.FStar_Syntax_Syntax.n
                                                                 in
                                                              match uu____14728
                                                              with
                                                              | FStar_Syntax_Syntax.Tm_fvar
                                                                  fv ->
                                                                  let uu____14734
                                                                    =
                                                                    FStar_Parser_Const.psconst
                                                                    "ignore"
                                                                     in
                                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                                    fv
                                                                    uu____14734
                                                              | uu____14736
                                                                  -> true
                                                               in
                                                            Prims.op_Negation
                                                              uu____14726)
                                                          in
                                                       if warn_effectful_args
                                                       then
                                                         (let uu____14740 =
                                                            let uu____14746 =
                                                              let uu____14748
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  e
                                                                 in
                                                              let uu____14750
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head2
                                                                 in
                                                              FStar_Util.format3
                                                                "Effectful argument %s (%s) to erased function %s, consider let binding it"
                                                                uu____14748
                                                                (c.FStar_TypeChecker_Common.eff_name).FStar_Ident.str
                                                                uu____14750
                                                               in
                                                            (FStar_Errors.Warning_EffectfulArgumentToErasedFunction,
                                                              uu____14746)
                                                             in
                                                          FStar_Errors.log_issue
                                                            e.FStar_Syntax_Syntax.pos
                                                            uu____14740)
                                                       else ();
                                                       (let uu____14757 =
                                                          FStar_TypeChecker_Env.debug
                                                            env
                                                            FStar_Options.Extreme
                                                           in
                                                        if uu____14757
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
                                                        let uu____14765 =
                                                          let uu____14774 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          (uu____14774, q)
                                                           in
                                                        ((FStar_Pervasives_Native.Some
                                                            (x,
                                                              (c.FStar_TypeChecker_Common.eff_name),
                                                              (c.FStar_TypeChecker_Common.res_typ),
                                                              e1)),
                                                          uu____14765)))))
                                               in
                                            let uu____14803 =
                                              let uu____14834 =
                                                let uu____14863 =
                                                  let uu____14874 =
                                                    let uu____14883 =
                                                      FStar_Syntax_Syntax.as_arg
                                                        head2
                                                       in
                                                    (uu____14883,
                                                      FStar_Pervasives_Native.None,
                                                      chead2)
                                                     in
                                                  uu____14874 ::
                                                    arg_comps_rev
                                                   in
                                                FStar_List.map map_fun
                                                  uu____14863
                                                 in
                                              FStar_All.pipe_left
                                                FStar_List.split uu____14834
                                               in
                                            match uu____14803 with
                                            | (lifted_args,reverse_args) ->
                                                let uu____15084 =
                                                  let uu____15085 =
                                                    FStar_List.hd
                                                      reverse_args
                                                     in
                                                  FStar_Pervasives_Native.fst
                                                    uu____15085
                                                   in
                                                let uu____15106 =
                                                  let uu____15107 =
                                                    FStar_List.tl
                                                      reverse_args
                                                     in
                                                  FStar_List.rev uu____15107
                                                   in
                                                (lifted_args, uu____15084,
                                                  uu____15106)
                                             in
                                          match uu____14519 with
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
                                                uu___6_15218 =
                                                match uu___6_15218 with
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
                                                      let uu____15279 =
                                                        let uu____15286 =
                                                          let uu____15287 =
                                                            let uu____15301 =
                                                              let uu____15304
                                                                =
                                                                let uu____15305
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_binder
                                                                    x
                                                                   in
                                                                [uu____15305]
                                                                 in
                                                              FStar_Syntax_Subst.close
                                                                uu____15304 e
                                                               in
                                                            ((false, [lb]),
                                                              uu____15301)
                                                             in
                                                          FStar_Syntax_Syntax.Tm_let
                                                            uu____15287
                                                           in
                                                        FStar_Syntax_Syntax.mk
                                                          uu____15286
                                                         in
                                                      uu____15279
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
                                     let uu____15357 =
                                       FStar_TypeChecker_Util.strengthen_precondition
                                         FStar_Pervasives_Native.None env app
                                         comp1 guard1
                                        in
                                     (match uu____15357 with
                                      | (comp2,g) ->
                                          ((let uu____15375 =
                                              FStar_TypeChecker_Env.debug env
                                                FStar_Options.Extreme
                                               in
                                            if uu____15375
                                            then
                                              let uu____15378 =
                                                FStar_Syntax_Print.term_to_string
                                                  app
                                                 in
                                              let uu____15380 =
                                                FStar_TypeChecker_Common.lcomp_to_string
                                                  comp2
                                                 in
                                              FStar_Util.print2
                                                "(d) Monadic app: type of app\n\t(%s)\n\t: %s\n"
                                                uu____15378 uu____15380
                                            else ());
                                           (app, comp2, g)))))))
                  in
               let rec tc_args head_info uu____15461 bs args1 =
                 match uu____15461 with
                 | (subst1,outargs,arg_rets,g,fvs) ->
                     (match (bs, args1) with
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____15600))::rest,
                         (uu____15602,FStar_Pervasives_Native.None )::uu____15603)
                          ->
                          let t =
                            FStar_Syntax_Subst.subst subst1
                              x.FStar_Syntax_Syntax.sort
                             in
                          let uu____15664 =
                            check_no_escape
                              (FStar_Pervasives_Native.Some head1) env fvs t
                             in
                          (match uu____15664 with
                           | (t1,g_ex) ->
                               let uu____15677 =
                                 FStar_TypeChecker_Util.new_implicit_var
                                   "Instantiating implicit argument in application"
                                   head1.FStar_Syntax_Syntax.pos env t1
                                  in
                               (match uu____15677 with
                                | (varg,uu____15698,implicits) ->
                                    let subst2 =
                                      (FStar_Syntax_Syntax.NT (x, varg)) ::
                                      subst1  in
                                    let arg =
                                      let uu____15726 =
                                        FStar_Syntax_Syntax.as_implicit true
                                         in
                                      (varg, uu____15726)  in
                                    let guard =
                                      FStar_List.fold_right
                                        FStar_TypeChecker_Env.conj_guard
                                        [g_ex; g] implicits
                                       in
                                    let uu____15735 =
                                      let uu____15770 =
                                        let uu____15781 =
                                          let uu____15790 =
                                            let uu____15791 =
                                              FStar_Syntax_Syntax.mk_Total t1
                                               in
                                            FStar_All.pipe_right uu____15791
                                              FStar_TypeChecker_Common.lcomp_of_comp
                                             in
                                          (arg, FStar_Pervasives_Native.None,
                                            uu____15790)
                                           in
                                        uu____15781 :: outargs  in
                                      (subst2, uu____15770, (arg ::
                                        arg_rets), guard, fvs)
                                       in
                                    tc_args head_info uu____15735 rest args1))
                      | ((x,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Meta tau))::rest,(uu____15837,FStar_Pervasives_Native.None
                                                                 )::uu____15838)
                          ->
                          let tau1 = FStar_Syntax_Subst.subst subst1 tau  in
                          let uu____15900 = tc_tactic env tau1  in
                          (match uu____15900 with
                           | (tau2,uu____15914,g_tau) ->
                               let t =
                                 FStar_Syntax_Subst.subst subst1
                                   x.FStar_Syntax_Syntax.sort
                                  in
                               let uu____15917 =
                                 check_no_escape
                                   (FStar_Pervasives_Native.Some head1) env
                                   fvs t
                                  in
                               (match uu____15917 with
                                | (t1,g_ex) ->
                                    let uu____15930 =
                                      let uu____15943 =
                                        let uu____15950 =
                                          let uu____15955 =
                                            FStar_Dyn.mkdyn env  in
                                          (uu____15955, tau2)  in
                                        FStar_Pervasives_Native.Some
                                          uu____15950
                                         in
                                      FStar_TypeChecker_Env.new_implicit_var_aux
                                        "Instantiating meta argument in application"
                                        head1.FStar_Syntax_Syntax.pos env t1
                                        FStar_Syntax_Syntax.Strict
                                        uu____15943
                                       in
                                    (match uu____15930 with
                                     | (varg,uu____15968,implicits) ->
                                         let subst2 =
                                           (FStar_Syntax_Syntax.NT (x, varg))
                                           :: subst1  in
                                         let arg =
                                           let uu____15996 =
                                             FStar_Syntax_Syntax.as_implicit
                                               true
                                              in
                                           (varg, uu____15996)  in
                                         let guard =
                                           FStar_List.fold_right
                                             FStar_TypeChecker_Env.conj_guard
                                             [g_ex; g; g_tau] implicits
                                            in
                                         let uu____16005 =
                                           let uu____16040 =
                                             let uu____16051 =
                                               let uu____16060 =
                                                 let uu____16061 =
                                                   FStar_Syntax_Syntax.mk_Total
                                                     t1
                                                    in
                                                 FStar_All.pipe_right
                                                   uu____16061
                                                   FStar_TypeChecker_Common.lcomp_of_comp
                                                  in
                                               (arg,
                                                 FStar_Pervasives_Native.None,
                                                 uu____16060)
                                                in
                                             uu____16051 :: outargs  in
                                           (subst2, uu____16040, (arg ::
                                             arg_rets), guard, fvs)
                                            in
                                         tc_args head_info uu____16005 rest
                                           args1)))
                      | ((x,aqual)::rest,(e,aq)::rest') ->
                          ((match (aqual, aq) with
                            | (uu____16177,FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta uu____16178)) ->
                                FStar_Errors.raise_error
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    "Inconsistent implicit qualifier; cannot apply meta arguments, just use #")
                                  e.FStar_Syntax_Syntax.pos
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Meta
                               uu____16189),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16190)) ->
                                ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit
                               uu____16198),FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu____16199)) ->
                                ()
                            | (FStar_Pervasives_Native.None
                               ,FStar_Pervasives_Native.None ) -> ()
                            | (FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Equality
                               ),FStar_Pervasives_Native.None ) -> ()
                            | uu____16214 ->
                                let uu____16223 =
                                  let uu____16229 =
                                    let uu____16231 =
                                      FStar_Syntax_Print.aqual_to_string
                                        aqual
                                       in
                                    let uu____16233 =
                                      FStar_Syntax_Print.aqual_to_string aq
                                       in
                                    let uu____16235 =
                                      FStar_Syntax_Print.bv_to_string x  in
                                    let uu____16237 =
                                      FStar_Syntax_Print.term_to_string e  in
                                    FStar_Util.format4
                                      "Inconsistent implicit qualifier; %s vs %s\nfor bvar %s and term %s"
                                      uu____16231 uu____16233 uu____16235
                                      uu____16237
                                     in
                                  (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                    uu____16229)
                                   in
                                FStar_Errors.raise_error uu____16223
                                  e.FStar_Syntax_Syntax.pos);
                           (let targ =
                              FStar_Syntax_Subst.subst subst1
                                x.FStar_Syntax_Syntax.sort
                               in
                            let aqual1 =
                              FStar_Syntax_Subst.subst_imp subst1 aqual  in
                            let x1 =
                              let uu___2179_16244 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___2179_16244.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___2179_16244.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = targ
                              }  in
                            (let uu____16246 =
                               FStar_TypeChecker_Env.debug env
                                 FStar_Options.Extreme
                                in
                             if uu____16246
                             then
                               let uu____16249 =
                                 FStar_Syntax_Print.bv_to_string x1  in
                               let uu____16251 =
                                 FStar_Syntax_Print.term_to_string
                                   x1.FStar_Syntax_Syntax.sort
                                  in
                               let uu____16253 =
                                 FStar_Syntax_Print.term_to_string e  in
                               let uu____16255 =
                                 FStar_Syntax_Print.subst_to_string subst1
                                  in
                               let uu____16257 =
                                 FStar_Syntax_Print.term_to_string targ  in
                               FStar_Util.print5
                                 "\tFormal is %s : %s\tType of arg %s (after subst %s) = %s\n"
                                 uu____16249 uu____16251 uu____16253
                                 uu____16255 uu____16257
                             else ());
                            (let uu____16262 =
                               check_no_escape
                                 (FStar_Pervasives_Native.Some head1) env fvs
                                 targ
                                in
                             match uu____16262 with
                             | (targ1,g_ex) ->
                                 let env1 =
                                   FStar_TypeChecker_Env.set_expected_typ env
                                     targ1
                                    in
                                 let env2 =
                                   let uu___2188_16277 = env1  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___2188_16277.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___2188_16277.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___2188_16277.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___2188_16277.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___2188_16277.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___2188_16277.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___2188_16277.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___2188_16277.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___2188_16277.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___2188_16277.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___2188_16277.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___2188_16277.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___2188_16277.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___2188_16277.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___2188_16277.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___2188_16277.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___2188_16277.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (is_eq aqual1);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___2188_16277.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___2188_16277.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___2188_16277.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___2188_16277.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___2188_16277.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___2188_16277.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___2188_16277.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___2188_16277.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___2188_16277.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___2188_16277.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___2188_16277.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___2188_16277.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___2188_16277.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___2188_16277.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___2188_16277.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___2188_16277.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___2188_16277.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___2188_16277.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___2188_16277.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___2188_16277.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___2188_16277.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___2188_16277.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___2188_16277.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___2188_16277.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___2188_16277.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___2188_16277.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___2188_16277.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___2188_16277.FStar_TypeChecker_Env.erasable_types_tab)
                                   }  in
                                 ((let uu____16279 =
                                     FStar_TypeChecker_Env.debug env2
                                       FStar_Options.High
                                      in
                                   if uu____16279
                                   then
                                     let uu____16282 =
                                       FStar_Syntax_Print.tag_of_term e  in
                                     let uu____16284 =
                                       FStar_Syntax_Print.term_to_string e
                                        in
                                     let uu____16286 =
                                       FStar_Syntax_Print.term_to_string
                                         targ1
                                        in
                                     FStar_Util.print3
                                       "Checking arg (%s) %s at type %s\n"
                                       uu____16282 uu____16284 uu____16286
                                   else ());
                                  (let uu____16291 = tc_term env2 e  in
                                   match uu____16291 with
                                   | (e1,c,g_e) ->
                                       let g1 =
                                         let uu____16308 =
                                           FStar_TypeChecker_Env.conj_guard g
                                             g_e
                                            in
                                         FStar_All.pipe_left
                                           (FStar_TypeChecker_Env.conj_guard
                                              g_ex) uu____16308
                                          in
                                       let arg = (e1, aq)  in
                                       let xterm =
                                         let uu____16331 =
                                           let uu____16334 =
                                             let uu____16343 =
                                               FStar_Syntax_Syntax.bv_to_name
                                                 x1
                                                in
                                             FStar_Syntax_Syntax.as_arg
                                               uu____16343
                                              in
                                           FStar_Pervasives_Native.fst
                                             uu____16334
                                            in
                                         (uu____16331, aq)  in
                                       let uu____16352 =
                                         (FStar_TypeChecker_Common.is_tot_or_gtot_lcomp
                                            c)
                                           ||
                                           (FStar_TypeChecker_Util.is_pure_or_ghost_effect
                                              env2
                                              c.FStar_TypeChecker_Common.eff_name)
                                          in
                                       if uu____16352
                                       then
                                         let subst2 =
                                           let uu____16362 = FStar_List.hd bs
                                              in
                                           maybe_extend_subst subst1
                                             uu____16362 e1
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
                      | (uu____16461,[]) ->
                          monadic_application head_info subst1 outargs
                            arg_rets g fvs bs
                      | ([],arg::uu____16497) ->
                          let uu____16548 =
                            monadic_application head_info subst1 outargs
                              arg_rets g fvs []
                             in
                          (match uu____16548 with
                           | (head2,chead1,ghead1) ->
                               let uu____16570 =
                                 let uu____16575 =
                                   FStar_TypeChecker_Common.lcomp_comp chead1
                                    in
                                 FStar_All.pipe_right uu____16575
                                   (fun uu____16592  ->
                                      match uu____16592 with
                                      | (c,g1) ->
                                          let uu____16603 =
                                            FStar_TypeChecker_Env.conj_guard
                                              ghead1 g1
                                             in
                                          (c, uu____16603))
                                  in
                               (match uu____16570 with
                                | (chead2,ghead2) ->
                                    let rec aux norm1 solve ghead3 tres =
                                      let tres1 =
                                        let uu____16646 =
                                          FStar_Syntax_Subst.compress tres
                                           in
                                        FStar_All.pipe_right uu____16646
                                          FStar_Syntax_Util.unrefine
                                         in
                                      match tres1.FStar_Syntax_Syntax.n with
                                      | FStar_Syntax_Syntax.Tm_arrow
                                          (bs1,cres') ->
                                          let uu____16677 =
                                            FStar_Syntax_Subst.open_comp bs1
                                              cres'
                                             in
                                          (match uu____16677 with
                                           | (bs2,cres'1) ->
                                               let head_info1 =
                                                 (head2, chead2, ghead3,
                                                   cres'1)
                                                  in
                                               ((let uu____16700 =
                                                   FStar_TypeChecker_Env.debug
                                                     env FStar_Options.Low
                                                    in
                                                 if uu____16700
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
                                      | uu____16747 when
                                          Prims.op_Negation norm1 ->
                                          let rec norm_tres tres2 =
                                            let tres3 =
                                              let uu____16755 =
                                                FStar_All.pipe_right tres2
                                                  (FStar_TypeChecker_Normalize.unfold_whnf
                                                     env)
                                                 in
                                              FStar_All.pipe_right
                                                uu____16755
                                                FStar_Syntax_Util.unascribe
                                               in
                                            let uu____16756 =
                                              let uu____16757 =
                                                FStar_Syntax_Subst.compress
                                                  tres3
                                                 in
                                              uu____16757.FStar_Syntax_Syntax.n
                                               in
                                            match uu____16756 with
                                            | FStar_Syntax_Syntax.Tm_refine
                                                ({
                                                   FStar_Syntax_Syntax.ppname
                                                     = uu____16760;
                                                   FStar_Syntax_Syntax.index
                                                     = uu____16761;
                                                   FStar_Syntax_Syntax.sort =
                                                     tres4;_},uu____16763)
                                                -> norm_tres tres4
                                            | uu____16771 -> tres3  in
                                          let uu____16772 = norm_tres tres1
                                             in
                                          aux true solve ghead3 uu____16772
                                      | uu____16774 when
                                          Prims.op_Negation solve ->
                                          let ghead4 =
                                            FStar_TypeChecker_Rel.solve_deferred_constraints
                                              env ghead3
                                             in
                                          aux norm1 true ghead4 tres1
                                      | uu____16777 ->
                                          let uu____16778 =
                                            let uu____16784 =
                                              let uu____16786 =
                                                FStar_TypeChecker_Normalize.term_to_string
                                                  env thead
                                                 in
                                              let uu____16788 =
                                                FStar_Util.string_of_int
                                                  n_args
                                                 in
                                              let uu____16790 =
                                                FStar_Syntax_Print.term_to_string
                                                  tres1
                                                 in
                                              FStar_Util.format3
                                                "Too many arguments to function of type %s; got %s arguments, remaining type is %s"
                                                uu____16786 uu____16788
                                                uu____16790
                                               in
                                            (FStar_Errors.Fatal_ToManyArgumentToFunction,
                                              uu____16784)
                                             in
                                          let uu____16794 =
                                            FStar_Syntax_Syntax.argpos arg
                                             in
                                          FStar_Errors.raise_error
                                            uu____16778 uu____16794
                                       in
                                    aux false false ghead2
                                      (FStar_Syntax_Util.comp_result chead2))))
                  in
               let rec check_function_app tf guard =
                 let uu____16824 =
                   let uu____16825 =
                     FStar_TypeChecker_Normalize.unfold_whnf env tf  in
                   uu____16825.FStar_Syntax_Syntax.n  in
                 match uu____16824 with
                 | FStar_Syntax_Syntax.Tm_uvar uu____16834 ->
                     let uu____16847 =
                       FStar_List.fold_right
                         (fun uu____16878  ->
                            fun uu____16879  ->
                              match uu____16879 with
                              | (bs,guard1) ->
                                  let uu____16906 =
                                    let uu____16919 =
                                      let uu____16920 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____16920
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____16919
                                     in
                                  (match uu____16906 with
                                   | (t,uu____16937,g) ->
                                       let uu____16951 =
                                         let uu____16954 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____16954 :: bs  in
                                       let uu____16955 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____16951, uu____16955))) args
                         ([], guard)
                        in
                     (match uu____16847 with
                      | (bs,guard1) ->
                          let uu____16972 =
                            let uu____16979 =
                              let uu____16992 =
                                let uu____16993 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____16993
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____16992
                               in
                            match uu____16979 with
                            | (t,uu____17010,g) ->
                                let uu____17024 = FStar_Options.ml_ish ()  in
                                if uu____17024
                                then
                                  let uu____17033 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17036 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17033, uu____17036)
                                else
                                  (let uu____17041 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17044 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17041, uu____17044))
                             in
                          (match uu____16972 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17063 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17063
                                 then
                                   let uu____17067 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____17069 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17071 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17067 uu____17069 uu____17071
                                 else ());
                                (let g =
                                   let uu____17077 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17077
                                    in
                                 let uu____17078 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17078))))
                 | FStar_Syntax_Syntax.Tm_app
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                          uu____17079;
                        FStar_Syntax_Syntax.pos = uu____17080;
                        FStar_Syntax_Syntax.vars = uu____17081;_},uu____17082)
                     ->
                     let uu____17119 =
                       FStar_List.fold_right
                         (fun uu____17150  ->
                            fun uu____17151  ->
                              match uu____17151 with
                              | (bs,guard1) ->
                                  let uu____17178 =
                                    let uu____17191 =
                                      let uu____17192 =
                                        FStar_Syntax_Util.type_u ()  in
                                      FStar_All.pipe_right uu____17192
                                        FStar_Pervasives_Native.fst
                                       in
                                    FStar_TypeChecker_Util.new_implicit_var
                                      "formal parameter"
                                      tf.FStar_Syntax_Syntax.pos env
                                      uu____17191
                                     in
                                  (match uu____17178 with
                                   | (t,uu____17209,g) ->
                                       let uu____17223 =
                                         let uu____17226 =
                                           FStar_Syntax_Syntax.null_binder t
                                            in
                                         uu____17226 :: bs  in
                                       let uu____17227 =
                                         FStar_TypeChecker_Env.conj_guard g
                                           guard1
                                          in
                                       (uu____17223, uu____17227))) args
                         ([], guard)
                        in
                     (match uu____17119 with
                      | (bs,guard1) ->
                          let uu____17244 =
                            let uu____17251 =
                              let uu____17264 =
                                let uu____17265 = FStar_Syntax_Util.type_u ()
                                   in
                                FStar_All.pipe_right uu____17265
                                  FStar_Pervasives_Native.fst
                                 in
                              FStar_TypeChecker_Util.new_implicit_var
                                "result type" tf.FStar_Syntax_Syntax.pos env
                                uu____17264
                               in
                            match uu____17251 with
                            | (t,uu____17282,g) ->
                                let uu____17296 = FStar_Options.ml_ish ()  in
                                if uu____17296
                                then
                                  let uu____17305 =
                                    FStar_Syntax_Util.ml_comp t r  in
                                  let uu____17308 =
                                    FStar_TypeChecker_Env.conj_guard guard1 g
                                     in
                                  (uu____17305, uu____17308)
                                else
                                  (let uu____17313 =
                                     FStar_Syntax_Syntax.mk_Total t  in
                                   let uu____17316 =
                                     FStar_TypeChecker_Env.conj_guard guard1
                                       g
                                      in
                                   (uu____17313, uu____17316))
                             in
                          (match uu____17244 with
                           | (cres,guard2) ->
                               let bs_cres = FStar_Syntax_Util.arrow bs cres
                                  in
                               ((let uu____17335 =
                                   FStar_All.pipe_left
                                     (FStar_TypeChecker_Env.debug env)
                                     FStar_Options.Extreme
                                    in
                                 if uu____17335
                                 then
                                   let uu____17339 =
                                     FStar_Syntax_Print.term_to_string head1
                                      in
                                   let uu____17341 =
                                     FStar_Syntax_Print.term_to_string tf  in
                                   let uu____17343 =
                                     FStar_Syntax_Print.term_to_string
                                       bs_cres
                                      in
                                   FStar_Util.print3
                                     "Forcing the type of %s from %s to %s\n"
                                     uu____17339 uu____17341 uu____17343
                                 else ());
                                (let g =
                                   let uu____17349 =
                                     FStar_TypeChecker_Rel.teq env tf bs_cres
                                      in
                                   FStar_TypeChecker_Rel.solve_deferred_constraints
                                     env uu____17349
                                    in
                                 let uu____17350 =
                                   FStar_TypeChecker_Env.conj_guard g guard2
                                    in
                                 check_function_app bs_cres uu____17350))))
                 | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                     let uu____17373 = FStar_Syntax_Subst.open_comp bs c  in
                     (match uu____17373 with
                      | (bs1,c1) ->
                          let head_info = (head1, chead, ghead, c1)  in
                          ((let uu____17396 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.Extreme
                               in
                            if uu____17396
                            then
                              let uu____17399 =
                                FStar_Syntax_Print.term_to_string head1  in
                              let uu____17401 =
                                FStar_Syntax_Print.term_to_string tf  in
                              let uu____17403 =
                                FStar_Syntax_Print.binders_to_string ", " bs1
                                 in
                              let uu____17406 =
                                FStar_Syntax_Print.comp_to_string c1  in
                              FStar_Util.print4
                                "######tc_args of head %s @ %s with formals=%s and result type=%s\n"
                                uu____17399 uu____17401 uu____17403
                                uu____17406
                            else ());
                           tc_args head_info ([], [], [], guard, []) bs1 args))
                 | FStar_Syntax_Syntax.Tm_refine (bv,uu____17452) ->
                     check_function_app bv.FStar_Syntax_Syntax.sort guard
                 | FStar_Syntax_Syntax.Tm_ascribed
                     (t,uu____17458,uu____17459) ->
                     check_function_app t guard
                 | uu____17500 ->
                     let uu____17501 =
                       FStar_TypeChecker_Err.expected_function_typ env tf  in
                     FStar_Errors.raise_error uu____17501
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
                  let uu____17584 =
                    FStar_List.fold_left2
                      (fun uu____17653  ->
                         fun uu____17654  ->
                           fun uu____17655  ->
                             match (uu____17653, uu____17654, uu____17655)
                             with
                             | ((seen,guard,ghost),(e,aq),(b,aq')) ->
                                 ((let uu____17808 =
                                     let uu____17810 =
                                       FStar_Syntax_Util.eq_aqual aq aq'  in
                                     uu____17810 <> FStar_Syntax_Util.Equal
                                      in
                                   if uu____17808
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_InconsistentImplicitQualifier,
                                         "Inconsistent implicit qualifiers")
                                       e.FStar_Syntax_Syntax.pos
                                   else ());
                                  (let uu____17816 =
                                     tc_check_tot_or_gtot_term env e
                                       b.FStar_Syntax_Syntax.sort
                                      in
                                   match uu____17816 with
                                   | (e1,c1,g) ->
                                       let short =
                                         FStar_TypeChecker_Util.short_circuit
                                           head1 seen
                                          in
                                       let g1 =
                                         let uu____17845 =
                                           FStar_TypeChecker_Env.guard_of_guard_formula
                                             short
                                            in
                                         FStar_TypeChecker_Env.imp_guard
                                           uu____17845 g
                                          in
                                       let ghost1 =
                                         ghost ||
                                           ((let uu____17850 =
                                               FStar_TypeChecker_Common.is_total_lcomp
                                                 c1
                                                in
                                             Prims.op_Negation uu____17850)
                                              &&
                                              (let uu____17853 =
                                                 FStar_TypeChecker_Util.is_pure_effect
                                                   env
                                                   c1.FStar_TypeChecker_Common.eff_name
                                                  in
                                               Prims.op_Negation uu____17853))
                                          in
                                       let uu____17855 =
                                         let uu____17866 =
                                           let uu____17877 =
                                             FStar_Syntax_Syntax.as_arg e1
                                              in
                                           [uu____17877]  in
                                         FStar_List.append seen uu____17866
                                          in
                                       let uu____17910 =
                                         FStar_TypeChecker_Env.conj_guard
                                           guard g1
                                          in
                                       (uu____17855, uu____17910, ghost1))))
                      ([], g_head, false) args bs
                     in
                  (match uu____17584 with
                   | (args1,guard,ghost) ->
                       let e =
                         FStar_Syntax_Syntax.mk_Tm_app head1 args1
                           FStar_Pervasives_Native.None r
                          in
                       let c1 =
                         if ghost
                         then
                           let uu____17978 =
                             FStar_Syntax_Syntax.mk_GTotal res_t  in
                           FStar_All.pipe_right uu____17978
                             FStar_TypeChecker_Common.lcomp_of_comp
                         else FStar_TypeChecker_Common.lcomp_of_comp c  in
                       let uu____17981 =
                         FStar_TypeChecker_Util.strengthen_precondition
                           FStar_Pervasives_Native.None env e c1 guard
                          in
                       (match uu____17981 with | (c2,g) -> (e, c2, g)))
              | uu____17998 ->
                  check_application_args env head1 chead g_head args
                    expected_topt

and (tc_pat :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.pat ->
        (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.bv Prims.list *
          FStar_Syntax_Syntax.term Prims.list * FStar_TypeChecker_Env.env *
          FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
          FStar_TypeChecker_Common.guard_t * Prims.bool))
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
            let uu____18096 = FStar_Syntax_Util.head_and_args t1  in
            match uu____18096 with
            | (head1,args) ->
                let uu____18139 =
                  let uu____18140 = FStar_Syntax_Subst.compress head1  in
                  uu____18140.FStar_Syntax_Syntax.n  in
                (match uu____18139 with
                 | FStar_Syntax_Syntax.Tm_uinst
                     ({
                        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar f;
                        FStar_Syntax_Syntax.pos = uu____18144;
                        FStar_Syntax_Syntax.vars = uu____18145;_},us)
                     -> unfold_once t1 f us args
                 | FStar_Syntax_Syntax.Tm_fvar f -> unfold_once t1 f [] args
                 | uu____18152 ->
                     if norm1
                     then t1
                     else
                       (let uu____18156 =
                          FStar_TypeChecker_Normalize.normalize
                            [FStar_TypeChecker_Env.HNF;
                            FStar_TypeChecker_Env.Unmeta;
                            FStar_TypeChecker_Env.Unascribe;
                            FStar_TypeChecker_Env.UnfoldUntil
                              FStar_Syntax_Syntax.delta_constant] env1 t1
                           in
                        aux true uu____18156))
          
          and unfold_once t f us args =
            let uu____18174 =
              FStar_TypeChecker_Env.is_type_constructor env1
                (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            if uu____18174
            then t
            else
              (let uu____18179 =
                 FStar_TypeChecker_Env.lookup_definition
                   [FStar_TypeChecker_Env.Unfold
                      FStar_Syntax_Syntax.delta_constant] env1
                   (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                  in
               match uu____18179 with
               | FStar_Pervasives_Native.None  -> t
               | FStar_Pervasives_Native.Some head_def_ts ->
                   let uu____18199 =
                     FStar_TypeChecker_Env.inst_tscheme_with head_def_ts us
                      in
                   (match uu____18199 with
                    | (uu____18204,head_def) ->
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
          let uu____18211 =
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta; FStar_TypeChecker_Env.Iota] env1
              scrutinee_t
             in
          aux false uu____18211  in
        let pat_typ_ok env1 pat_t1 scrutinee_t =
          (let uu____18230 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____18230
           then
             let uu____18235 = FStar_Syntax_Print.term_to_string pat_t1  in
             let uu____18237 = FStar_Syntax_Print.term_to_string scrutinee_t
                in
             FStar_Util.print2 "$$$$$$$$$$$$pat_typ_ok? %s vs. %s\n"
               uu____18235 uu____18237
           else ());
          (let fail2 msg =
             let msg1 =
               let uu____18257 = FStar_Syntax_Print.term_to_string pat_t1  in
               let uu____18259 =
                 FStar_Syntax_Print.term_to_string scrutinee_t  in
               FStar_Util.format3
                 "Type of pattern (%s) does not match type of scrutinee (%s)%s"
                 uu____18257 uu____18259 msg
                in
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_MismatchedPatternType, msg1)
               p0.FStar_Syntax_Syntax.p
              in
           let uu____18263 = FStar_Syntax_Util.head_and_args scrutinee_t  in
           match uu____18263 with
           | (head_s,args_s) ->
               let pat_t2 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env1 pat_t1
                  in
               let uu____18307 = FStar_Syntax_Util.un_uinst head_s  in
               (match uu____18307 with
                | {
                    FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                      uu____18308;
                    FStar_Syntax_Syntax.pos = uu____18309;
                    FStar_Syntax_Syntax.vars = uu____18310;_} ->
                    let uu____18313 = FStar_Syntax_Util.head_and_args pat_t2
                       in
                    (match uu____18313 with
                     | (head_p,args_p) ->
                         let uu____18356 =
                           FStar_TypeChecker_Rel.teq_nosmt_force env1 head_p
                             head_s
                            in
                         if uu____18356
                         then
                           let uu____18359 =
                             let uu____18360 =
                               FStar_Syntax_Util.un_uinst head_p  in
                             uu____18360.FStar_Syntax_Syntax.n  in
                           (match uu____18359 with
                            | FStar_Syntax_Syntax.Tm_fvar f ->
                                ((let uu____18365 =
                                    let uu____18367 =
                                      let uu____18369 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.is_type_constructor
                                        env1 uu____18369
                                       in
                                    FStar_All.pipe_left Prims.op_Negation
                                      uu____18367
                                     in
                                  if uu____18365
                                  then
                                    fail2
                                      "Pattern matching a non-inductive type"
                                  else ());
                                 if
                                   (FStar_List.length args_p) <>
                                     (FStar_List.length args_s)
                                 then fail2 ""
                                 else ();
                                 (let uu____18397 =
                                    let uu____18422 =
                                      let uu____18426 =
                                        FStar_Syntax_Syntax.lid_of_fv f  in
                                      FStar_TypeChecker_Env.num_inductive_ty_params
                                        env1 uu____18426
                                       in
                                    match uu____18422 with
                                    | FStar_Pervasives_Native.None  ->
                                        (args_p, args_s)
                                    | FStar_Pervasives_Native.Some n1 ->
                                        let uu____18475 =
                                          FStar_Util.first_N n1 args_p  in
                                        (match uu____18475 with
                                         | (params_p,uu____18533) ->
                                             let uu____18574 =
                                               FStar_Util.first_N n1 args_s
                                                in
                                             (match uu____18574 with
                                              | (params_s,uu____18632) ->
                                                  (params_p, params_s)))
                                     in
                                  match uu____18397 with
                                  | (params_p,params_s) ->
                                      FStar_List.fold_left2
                                        (fun out  ->
                                           fun uu____18761  ->
                                             fun uu____18762  ->
                                               match (uu____18761,
                                                       uu____18762)
                                               with
                                               | ((p,uu____18796),(s,uu____18798))
                                                   ->
                                                   let uu____18831 =
                                                     FStar_TypeChecker_Rel.teq_nosmt
                                                       env1 p s
                                                      in
                                                   (match uu____18831 with
                                                    | FStar_Pervasives_Native.None
                                                         ->
                                                        let uu____18834 =
                                                          let uu____18836 =
                                                            FStar_Syntax_Print.term_to_string
                                                              p
                                                             in
                                                          let uu____18838 =
                                                            FStar_Syntax_Print.term_to_string
                                                              s
                                                             in
                                                          FStar_Util.format2
                                                            "; parameter %s <> parameter %s"
                                                            uu____18836
                                                            uu____18838
                                                           in
                                                        fail2 uu____18834
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
                            | uu____18843 ->
                                fail2 "Pattern matching a non-inductive type")
                         else
                           (let uu____18847 =
                              let uu____18849 =
                                FStar_Syntax_Print.term_to_string head_p  in
                              let uu____18851 =
                                FStar_Syntax_Print.term_to_string head_s  in
                              FStar_Util.format2 "; head mismatch %s vs %s"
                                uu____18849 uu____18851
                               in
                            fail2 uu____18847))
                | uu____18854 ->
                    let uu____18855 =
                      FStar_TypeChecker_Rel.teq_nosmt env1 pat_t2 scrutinee_t
                       in
                    (match uu____18855 with
                     | FStar_Pervasives_Native.None  -> fail2 ""
                     | FStar_Pervasives_Native.Some g ->
                         let g1 =
                           FStar_TypeChecker_Rel.discharge_guard_no_smt env1
                             g
                            in
                         g1)))
           in
        let type_of_simple_pat env1 e =
          let uu____18898 = FStar_Syntax_Util.head_and_args e  in
          match uu____18898 with
          | (head1,args) ->
              (match head1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_fvar f ->
                   let uu____18968 =
                     FStar_TypeChecker_Env.lookup_datacon env1
                       (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18968 with
                    | (us,t_f) ->
                        let uu____18988 = FStar_Syntax_Util.arrow_formals t_f
                           in
                        (match uu____18988 with
                         | (formals,t) ->
                             let erasable1 =
                               FStar_TypeChecker_Env.non_informative env1 t
                                in
                             (if
                                (FStar_List.length formals) <>
                                  (FStar_List.length args)
                              then
                                fail1
                                  "Pattern is not a fully-applied data constructor"
                              else ();
                              (let rec aux uu____19125 formals1 args1 =
                                 match uu____19125 with
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
                                          let uu____19276 =
                                            FStar_Syntax_Subst.subst subst1 t
                                             in
                                          (pat_e, uu____19276, bvs, guard,
                                            erasable1)
                                      | ((f1,uu____19283)::formals2,(a,imp_a)::args2)
                                          ->
                                          let t_f1 =
                                            FStar_Syntax_Subst.subst subst1
                                              f1.FStar_Syntax_Syntax.sort
                                             in
                                          let uu____19341 =
                                            let uu____19362 =
                                              let uu____19363 =
                                                FStar_Syntax_Subst.compress a
                                                 in
                                              uu____19363.FStar_Syntax_Syntax.n
                                               in
                                            match uu____19362 with
                                            | FStar_Syntax_Syntax.Tm_name x
                                                ->
                                                let x1 =
                                                  let uu___2495_19388 = x  in
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      =
                                                      (uu___2495_19388.FStar_Syntax_Syntax.ppname);
                                                    FStar_Syntax_Syntax.index
                                                      =
                                                      (uu___2495_19388.FStar_Syntax_Syntax.index);
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
                                                uu____19411 ->
                                                let env2 =
                                                  FStar_TypeChecker_Env.set_expected_typ
                                                    env1 t_f1
                                                   in
                                                let uu____19425 =
                                                  tc_tot_or_gtot_term env2 a
                                                   in
                                                (match uu____19425 with
                                                 | (a1,uu____19453,g) ->
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
                                            | uu____19477 ->
                                                fail1 "Not a simple pattern"
                                             in
                                          (match uu____19341 with
                                           | (a1,subst2,bvs1,g) ->
                                               let uu____19542 =
                                                 let uu____19565 =
                                                   FStar_TypeChecker_Env.conj_guard
                                                     g guard
                                                    in
                                                 (subst2,
                                                   (FStar_List.append
                                                      args_out [a1]), bvs1,
                                                   uu____19565)
                                                  in
                                               aux uu____19542 formals2 args2)
                                      | uu____19604 ->
                                          fail1 "Not a fully applued pattern")
                                  in
                               aux
                                 ([], [], [],
                                   FStar_TypeChecker_Env.trivial_guard)
                                 formals args))))
               | uu____19663 -> fail1 "Not a simple pattern")
           in
        let rec check_nested_pattern env1 p t =
          (let uu____19729 =
             FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1)
               (FStar_Options.Other "Patterns")
              in
           if uu____19729
           then
             let uu____19734 = FStar_Syntax_Print.pat_to_string p  in
             let uu____19736 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.print2 "Checking pattern %s at type %s\n" uu____19734
               uu____19736
           else ());
          (let id1 =
             FStar_Syntax_Syntax.fvar FStar_Parser_Const.id_lid
               (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
               FStar_Pervasives_Native.None
              in
           let mk_disc_t disc inner_t =
             let x_b =
               let uu____19761 =
                 FStar_Syntax_Syntax.gen_bv "x" FStar_Pervasives_Native.None
                   t
                  in
               FStar_All.pipe_right uu____19761 FStar_Syntax_Syntax.mk_binder
                in
             let tm =
               let uu____19772 =
                 let uu____19777 =
                   let uu____19778 =
                     let uu____19787 =
                       let uu____19788 =
                         FStar_All.pipe_right x_b FStar_Pervasives_Native.fst
                          in
                       FStar_All.pipe_right uu____19788
                         FStar_Syntax_Syntax.bv_to_name
                        in
                     FStar_All.pipe_right uu____19787
                       FStar_Syntax_Syntax.as_arg
                      in
                   [uu____19778]  in
                 FStar_Syntax_Syntax.mk_Tm_app disc uu____19777  in
               uu____19772 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             let tm1 =
               let uu____19824 =
                 let uu____19829 =
                   let uu____19830 =
                     FStar_All.pipe_right tm FStar_Syntax_Syntax.as_arg  in
                   [uu____19830]  in
                 FStar_Syntax_Syntax.mk_Tm_app inner_t uu____19829  in
               uu____19824 FStar_Pervasives_Native.None
                 FStar_Range.dummyRange
                in
             FStar_Syntax_Util.abs [x_b] tm1 FStar_Pervasives_Native.None  in
           match p.FStar_Syntax_Syntax.v with
           | FStar_Syntax_Syntax.Pat_dot_term uu____19892 ->
               let uu____19899 =
                 let uu____19901 = FStar_Syntax_Print.pat_to_string p  in
                 FStar_Util.format1
                   "Impossible: Expected an undecorated pattern, got %s"
                   uu____19901
                  in
               failwith uu____19899
           | FStar_Syntax_Syntax.Pat_wild x ->
               let x1 =
                 let uu___2534_19923 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2534_19923.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2534_19923.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19924 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id1], uu____19924,
                 (let uu___2537_19931 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_wild x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2537_19931.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_var x ->
               let x1 =
                 let uu___2541_19935 = x  in
                 {
                   FStar_Syntax_Syntax.ppname =
                     (uu___2541_19935.FStar_Syntax_Syntax.ppname);
                   FStar_Syntax_Syntax.index =
                     (uu___2541_19935.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = t
                 }  in
               let uu____19936 = FStar_Syntax_Syntax.bv_to_name x1  in
               ([x1], [id1], uu____19936,
                 (let uu___2544_19943 = p  in
                  {
                    FStar_Syntax_Syntax.v = (FStar_Syntax_Syntax.Pat_var x1);
                    FStar_Syntax_Syntax.p =
                      (uu___2544_19943.FStar_Syntax_Syntax.p)
                  }), FStar_TypeChecker_Env.trivial_guard, false)
           | FStar_Syntax_Syntax.Pat_constant uu____19945 ->
               let uu____19946 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1 p  in
               (match uu____19946 with
                | (uu____19975,e_c,uu____19977,uu____19978) ->
                    let uu____19983 = tc_tot_or_gtot_term env1 e_c  in
                    (match uu____19983 with
                     | (e_c1,lc,g) ->
                         (FStar_TypeChecker_Rel.force_trivial_guard env1 g;
                          (let expected_t =
                             expected_pat_typ env1 p0.FStar_Syntax_Syntax.p t
                              in
                           (let uu____20013 =
                              let uu____20015 =
                                FStar_TypeChecker_Rel.teq_nosmt_force env1
                                  lc.FStar_TypeChecker_Common.res_typ
                                  expected_t
                                 in
                              Prims.op_Negation uu____20015  in
                            if uu____20013
                            then
                              let uu____20018 =
                                let uu____20020 =
                                  FStar_Syntax_Print.term_to_string
                                    lc.FStar_TypeChecker_Common.res_typ
                                   in
                                let uu____20022 =
                                  FStar_Syntax_Print.term_to_string
                                    expected_t
                                   in
                                FStar_Util.format2
                                  "Type of pattern (%s) does not match type of scrutinee (%s)"
                                  uu____20020 uu____20022
                                 in
                              fail1 uu____20018
                            else ());
                           ([], [], e_c1, p,
                             FStar_TypeChecker_Env.trivial_guard, false)))))
           | FStar_Syntax_Syntax.Pat_cons (fv,sub_pats) ->
               let simple_pat =
                 let simple_sub_pats =
                   FStar_List.map
                     (fun uu____20084  ->
                        match uu____20084 with
                        | (p1,b) ->
                            (match p1.FStar_Syntax_Syntax.v with
                             | FStar_Syntax_Syntax.Pat_dot_term uu____20114
                                 -> (p1, b)
                             | uu____20124 ->
                                 let uu____20125 =
                                   let uu____20128 =
                                     let uu____20129 =
                                       FStar_Syntax_Syntax.new_bv
                                         (FStar_Pervasives_Native.Some
                                            (p1.FStar_Syntax_Syntax.p))
                                         FStar_Syntax_Syntax.tun
                                        in
                                     FStar_Syntax_Syntax.Pat_var uu____20129
                                      in
                                   FStar_Syntax_Syntax.withinfo uu____20128
                                     p1.FStar_Syntax_Syntax.p
                                    in
                                 (uu____20125, b))) sub_pats
                    in
                 let uu___2572_20133 = p  in
                 {
                   FStar_Syntax_Syntax.v =
                     (FStar_Syntax_Syntax.Pat_cons (fv, simple_sub_pats));
                   FStar_Syntax_Syntax.p =
                     (uu___2572_20133.FStar_Syntax_Syntax.p)
                 }  in
               let sub_pats1 =
                 FStar_All.pipe_right sub_pats
                   (FStar_List.filter
                      (fun uu____20178  ->
                         match uu____20178 with
                         | (x,uu____20188) ->
                             (match x.FStar_Syntax_Syntax.v with
                              | FStar_Syntax_Syntax.Pat_dot_term uu____20196
                                  -> false
                              | uu____20204 -> true)))
                  in
               let uu____20206 =
                 FStar_TypeChecker_PatternUtils.pat_as_exp false env1
                   simple_pat
                  in
               (match uu____20206 with
                | (simple_bvs,simple_pat_e,g0,simple_pat_elab) ->
                    (if
                       (FStar_List.length simple_bvs) <>
                         (FStar_List.length sub_pats1)
                     then
                       (let uu____20250 =
                          let uu____20252 =
                            FStar_Range.string_of_range
                              p.FStar_Syntax_Syntax.p
                             in
                          let uu____20254 =
                            FStar_Syntax_Print.pat_to_string simple_pat  in
                          let uu____20256 =
                            FStar_Util.string_of_int
                              (FStar_List.length sub_pats1)
                             in
                          let uu____20263 =
                            FStar_Util.string_of_int
                              (FStar_List.length simple_bvs)
                             in
                          FStar_Util.format4
                            "(%s) Impossible: pattern bvar mismatch: %s; expected %s sub pats; got %s"
                            uu____20252 uu____20254 uu____20256 uu____20263
                           in
                        failwith uu____20250)
                     else ();
                     (let uu____20268 =
                        let uu____20280 =
                          type_of_simple_pat env1 simple_pat_e  in
                        match uu____20280 with
                        | (simple_pat_e1,simple_pat_t,simple_bvs1,guard,erasable1)
                            ->
                            let g' =
                              let uu____20317 =
                                expected_pat_typ env1
                                  p0.FStar_Syntax_Syntax.p t
                                 in
                              pat_typ_ok env1 simple_pat_t uu____20317  in
                            let guard1 =
                              FStar_TypeChecker_Env.conj_guard guard g'  in
                            ((let uu____20320 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env1)
                                  (FStar_Options.Other "Patterns")
                                 in
                              if uu____20320
                              then
                                let uu____20325 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_e1
                                   in
                                let uu____20327 =
                                  FStar_Syntax_Print.term_to_string
                                    simple_pat_t
                                   in
                                let uu____20329 =
                                  let uu____20331 =
                                    FStar_List.map
                                      (fun x  ->
                                         let uu____20339 =
                                           let uu____20341 =
                                             FStar_Syntax_Print.bv_to_string
                                               x
                                              in
                                           let uu____20343 =
                                             let uu____20345 =
                                               let uu____20347 =
                                                 FStar_Syntax_Print.term_to_string
                                                   x.FStar_Syntax_Syntax.sort
                                                  in
                                               Prims.op_Hat uu____20347 ")"
                                                in
                                             Prims.op_Hat " : " uu____20345
                                              in
                                           Prims.op_Hat uu____20341
                                             uu____20343
                                            in
                                         Prims.op_Hat "(" uu____20339)
                                      simple_bvs1
                                     in
                                  FStar_All.pipe_right uu____20331
                                    (FStar_String.concat " ")
                                   in
                                FStar_Util.print3
                                  "$$$$$$$$$$$$Checked simple pattern %s at type %s with bvs=%s\n"
                                  uu____20325 uu____20327 uu____20329
                              else ());
                             (simple_pat_e1, simple_bvs1, guard1, erasable1))
                         in
                      match uu____20268 with
                      | (simple_pat_e1,simple_bvs1,g1,erasable1) ->
                          let uu____20390 =
                            let uu____20422 =
                              let uu____20454 =
                                FStar_TypeChecker_Env.conj_guard g0 g1  in
                              (env1, [], [], [], [], uu____20454, erasable1,
                                Prims.int_zero)
                               in
                            FStar_List.fold_left2
                              (fun uu____20536  ->
                                 fun uu____20537  ->
                                   fun x  ->
                                     match (uu____20536, uu____20537) with
                                     | ((env2,bvs,tms,pats,subst1,g,erasable2,i),
                                        (p1,b)) ->
                                         let expected_t =
                                           FStar_Syntax_Subst.subst subst1
                                             x.FStar_Syntax_Syntax.sort
                                            in
                                         let uu____20721 =
                                           check_nested_pattern env2 p1
                                             expected_t
                                            in
                                         (match uu____20721 with
                                          | (bvs_p,tms_p,e_p,p2,g',erasable_p)
                                              ->
                                              let env3 =
                                                FStar_TypeChecker_Env.push_bvs
                                                  env2 bvs_p
                                                 in
                                              let tms_p1 =
                                                let disc_tm =
                                                  let uu____20791 =
                                                    FStar_Syntax_Syntax.lid_of_fv
                                                      fv
                                                     in
                                                  FStar_TypeChecker_Util.get_field_projector_name
                                                    env3 uu____20791 i
                                                   in
                                                let uu____20792 =
                                                  let uu____20801 =
                                                    let uu____20806 =
                                                      FStar_Syntax_Syntax.fvar
                                                        disc_tm
                                                        (FStar_Syntax_Syntax.Delta_constant_at_level
                                                           Prims.int_one)
                                                        FStar_Pervasives_Native.None
                                                       in
                                                    mk_disc_t uu____20806  in
                                                  FStar_List.map uu____20801
                                                   in
                                                FStar_All.pipe_right tms_p
                                                  uu____20792
                                                 in
                                              let uu____20812 =
                                                FStar_TypeChecker_Env.conj_guard
                                                  g g'
                                                 in
                                              (env3,
                                                (FStar_List.append bvs bvs_p),
                                                (FStar_List.append tms tms_p1),
                                                (FStar_List.append pats
                                                   [(p2, b)]),
                                                ((FStar_Syntax_Syntax.NT
                                                    (x, e_p)) :: subst1),
                                                uu____20812,
                                                (erasable2 || erasable_p),
                                                (i + Prims.int_one))))
                              uu____20422 sub_pats1 simple_bvs1
                             in
                          (match uu____20390 with
                           | (_env,bvs,tms,checked_sub_pats,subst1,g,erasable2,uu____20871)
                               ->
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
                                              let uu___2656_21047 = hd1  in
                                              {
                                                FStar_Syntax_Syntax.v =
                                                  (FStar_Syntax_Syntax.Pat_dot_term
                                                     (x, e1));
                                                FStar_Syntax_Syntax.p =
                                                  (uu___2656_21047.FStar_Syntax_Syntax.p)
                                              }  in
                                            let uu____21052 =
                                              aux simple_pats1 bvs1 sub_pats2
                                               in
                                            (hd2, b) :: uu____21052
                                        | FStar_Syntax_Syntax.Pat_var x ->
                                            (match (bvs1, sub_pats2) with
                                             | (x'::bvs2,(hd2,uu____21096)::sub_pats3)
                                                 when
                                                 FStar_Syntax_Syntax.bv_eq x
                                                   x'
                                                 ->
                                                 let uu____21133 =
                                                   aux simple_pats1 bvs2
                                                     sub_pats3
                                                    in
                                                 (hd2, b) :: uu____21133
                                             | uu____21153 ->
                                                 failwith
                                                   "Impossible: simple pat variable mismatch")
                                        | uu____21179 ->
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
                                     let uu___2677_21222 = pat  in
                                     {
                                       FStar_Syntax_Syntax.v =
                                         (FStar_Syntax_Syntax.Pat_cons
                                            (fv1, nested_pats));
                                       FStar_Syntax_Syntax.p =
                                         (uu___2677_21222.FStar_Syntax_Syntax.p)
                                     }
                                 | uu____21234 -> failwith "Impossible"  in
                               let uu____21238 =
                                 reconstruct_nested_pat simple_pat_elab  in
                               (bvs, tms, pat_e, uu____21238, g, erasable2))))))
           in
        (let uu____21245 =
           FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
             (FStar_Options.Other "Patterns")
            in
         if uu____21245
         then
           let uu____21250 = FStar_Syntax_Print.pat_to_string p0  in
           FStar_Util.print1 "Checking pattern: %s\n" uu____21250
         else ());
        (let uu____21255 =
           let uu____21273 =
             let uu___2682_21274 =
               let uu____21275 = FStar_TypeChecker_Env.clear_expected_typ env
                  in
               FStar_All.pipe_right uu____21275 FStar_Pervasives_Native.fst
                in
             {
               FStar_TypeChecker_Env.solver =
                 (uu___2682_21274.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range =
                 (uu___2682_21274.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (uu___2682_21274.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma =
                 (uu___2682_21274.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (uu___2682_21274.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (uu___2682_21274.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (uu___2682_21274.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (uu___2682_21274.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (uu___2682_21274.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (uu___2682_21274.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.is_pattern =
                 (uu___2682_21274.FStar_TypeChecker_Env.is_pattern);
               FStar_TypeChecker_Env.instantiate_imp =
                 (uu___2682_21274.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (uu___2682_21274.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (uu___2682_21274.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (uu___2682_21274.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (uu___2682_21274.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (uu___2682_21274.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq = true;
               FStar_TypeChecker_Env.is_iface =
                 (uu___2682_21274.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit =
                 (uu___2682_21274.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax =
                 (uu___2682_21274.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (uu___2682_21274.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (uu___2682_21274.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (uu___2682_21274.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (uu___2682_21274.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (uu___2682_21274.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.tc_term =
                 (uu___2682_21274.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.type_of =
                 (uu___2682_21274.FStar_TypeChecker_Env.type_of);
               FStar_TypeChecker_Env.universe_of =
                 (uu___2682_21274.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.check_type_of =
                 (uu___2682_21274.FStar_TypeChecker_Env.check_type_of);
               FStar_TypeChecker_Env.use_bv_sorts =
                 (uu___2682_21274.FStar_TypeChecker_Env.use_bv_sorts);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (uu___2682_21274.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (uu___2682_21274.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (uu___2682_21274.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (uu___2682_21274.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (uu___2682_21274.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (uu___2682_21274.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (uu___2682_21274.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.postprocess =
                 (uu___2682_21274.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.is_native_tactic =
                 (uu___2682_21274.FStar_TypeChecker_Env.is_native_tactic);
               FStar_TypeChecker_Env.identifier_info =
                 (uu___2682_21274.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (uu___2682_21274.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv =
                 (uu___2682_21274.FStar_TypeChecker_Env.dsenv);
               FStar_TypeChecker_Env.nbe =
                 (uu___2682_21274.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (uu___2682_21274.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (uu___2682_21274.FStar_TypeChecker_Env.erasable_types_tab)
             }  in
           let uu____21291 =
             FStar_TypeChecker_PatternUtils.elaborate_pat env p0  in
           check_nested_pattern uu____21273 uu____21291 pat_t  in
         match uu____21255 with
         | (bvs,tms,pat_e,pat,g,erasable1) ->
             ((let uu____21330 =
                 FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
                   (FStar_Options.Other "Patterns")
                  in
               if uu____21330
               then
                 let uu____21335 = FStar_Syntax_Print.pat_to_string pat  in
                 let uu____21337 = FStar_Syntax_Print.term_to_string pat_e
                    in
                 FStar_Util.print2
                   "Done checking pattern %s as expression %s\n" uu____21335
                   uu____21337
               else ());
              (let uu____21342 = FStar_TypeChecker_Env.push_bvs env bvs  in
               let uu____21343 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.Beta] env pat_e
                  in
               (pat, bvs, tms, uu____21342, pat_e, uu____21343, g, erasable1))))

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
          FStar_TypeChecker_Common.guard_t * Prims.bool))
  =
  fun scrutinee  ->
    fun env  ->
      fun branch1  ->
        let uu____21395 = FStar_Syntax_Subst.open_branch branch1  in
        match uu____21395 with
        | (pattern,when_clause,branch_exp) ->
            let uu____21444 = branch1  in
            (match uu____21444 with
             | (cpat,uu____21489,cbr) ->
                 let pat_t = scrutinee.FStar_Syntax_Syntax.sort  in
                 let scrutinee_tm = FStar_Syntax_Syntax.bv_to_name scrutinee
                    in
                 let uu____21511 =
                   let uu____21518 =
                     FStar_TypeChecker_Env.push_bv env scrutinee  in
                   FStar_All.pipe_right uu____21518
                     FStar_TypeChecker_Env.clear_expected_typ
                    in
                 (match uu____21511 with
                  | (scrutinee_env,uu____21555) ->
                      let uu____21560 = tc_pat env pat_t pattern  in
                      (match uu____21560 with
                       | (pattern1,pat_bvs1,pat_bv_tms,pat_env,pat_exp,norm_pat_exp,guard_pat,erasable1)
                           ->
                           ((let uu____21630 =
                               FStar_All.pipe_left
                                 (FStar_TypeChecker_Env.debug env)
                                 FStar_Options.Extreme
                                in
                             if uu____21630
                             then
                               let uu____21634 =
                                 FStar_Syntax_Print.pat_to_string pattern1
                                  in
                               let uu____21636 =
                                 FStar_Syntax_Print.bvs_to_string ";"
                                   pat_bvs1
                                  in
                               let uu____21639 =
                                 FStar_List.fold_left
                                   (fun s  ->
                                      fun t  ->
                                        let uu____21648 =
                                          let uu____21650 =
                                            FStar_Syntax_Print.term_to_string
                                              t
                                             in
                                          Prims.op_Hat ";" uu____21650  in
                                        Prims.op_Hat s uu____21648) ""
                                   pat_bv_tms
                                  in
                               FStar_Util.print3
                                 "tc_eqn: typechecked pattern %s with bvs %s and pat_bv_tms %s"
                                 uu____21634 uu____21636 uu____21639
                             else ());
                            (let uu____21657 =
                               match when_clause with
                               | FStar_Pervasives_Native.None  ->
                                   (FStar_Pervasives_Native.None,
                                     FStar_TypeChecker_Env.trivial_guard)
                               | FStar_Pervasives_Native.Some e ->
                                   let uu____21687 =
                                     FStar_TypeChecker_Env.should_verify env
                                      in
                                   if uu____21687
                                   then
                                     FStar_Errors.raise_error
                                       (FStar_Errors.Fatal_WhenClauseNotSupported,
                                         "When clauses are not yet supported in --verify mode; they will be some day")
                                       e.FStar_Syntax_Syntax.pos
                                   else
                                     (let uu____21710 =
                                        let uu____21717 =
                                          FStar_TypeChecker_Env.set_expected_typ
                                            pat_env FStar_Syntax_Util.t_bool
                                           in
                                        tc_term uu____21717 e  in
                                      match uu____21710 with
                                      | (e1,c,g) ->
                                          ((FStar_Pervasives_Native.Some e1),
                                            g))
                                in
                             match uu____21657 with
                             | (when_clause1,g_when) ->
                                 let uu____21774 = tc_term pat_env branch_exp
                                    in
                                 (match uu____21774 with
                                  | (branch_exp1,c,g_branch) ->
                                      (FStar_TypeChecker_Env.def_check_guard_wf
                                         cbr.FStar_Syntax_Syntax.pos
                                         "tc_eqn.1" pat_env g_branch;
                                       (let when_condition =
                                          match when_clause1 with
                                          | FStar_Pervasives_Native.None  ->
                                              FStar_Pervasives_Native.None
                                          | FStar_Pervasives_Native.Some w ->
                                              let uu____21833 =
                                                FStar_Syntax_Util.mk_eq2
                                                  FStar_Syntax_Syntax.U_zero
                                                  FStar_Syntax_Util.t_bool w
                                                  FStar_Syntax_Util.exp_true_bool
                                                 in
                                              FStar_All.pipe_left
                                                (fun _21844  ->
                                                   FStar_Pervasives_Native.Some
                                                     _21844) uu____21833
                                           in
                                        let uu____21845 =
                                          let eqs =
                                            let uu____21867 =
                                              let uu____21869 =
                                                FStar_TypeChecker_Env.should_verify
                                                  env
                                                 in
                                              Prims.op_Negation uu____21869
                                               in
                                            if uu____21867
                                            then FStar_Pervasives_Native.None
                                            else
                                              (let e =
                                                 FStar_Syntax_Subst.compress
                                                   pat_exp
                                                  in
                                               match e.FStar_Syntax_Syntax.n
                                               with
                                               | FStar_Syntax_Syntax.Tm_uvar
                                                   uu____21885 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_constant
                                                   uu____21900 ->
                                                   FStar_Pervasives_Native.None
                                               | FStar_Syntax_Syntax.Tm_fvar
                                                   uu____21903 ->
                                                   FStar_Pervasives_Native.None
                                               | uu____21906 ->
                                                   let uu____21907 =
                                                     let uu____21910 =
                                                       env.FStar_TypeChecker_Env.universe_of
                                                         env pat_t
                                                        in
                                                     FStar_Syntax_Util.mk_eq2
                                                       uu____21910 pat_t
                                                       scrutinee_tm e
                                                      in
                                                   FStar_Pervasives_Native.Some
                                                     uu____21907)
                                             in
                                          let uu____21913 =
                                            FStar_TypeChecker_Util.strengthen_precondition
                                              FStar_Pervasives_Native.None
                                              env branch_exp1 c g_branch
                                             in
                                          match uu____21913 with
                                          | (c1,g_branch1) ->
                                              let uu____21940 =
                                                let env1 =
                                                  let uu____21946 =
                                                    FStar_All.pipe_right
                                                      pat_bvs1
                                                      (FStar_List.map
                                                         FStar_Syntax_Syntax.mk_binder)
                                                     in
                                                  FStar_TypeChecker_Env.push_binders
                                                    scrutinee_env uu____21946
                                                   in
                                                match (eqs, when_condition)
                                                with
                                                | uu____21961 when
                                                    let uu____21974 =
                                                      FStar_TypeChecker_Env.should_verify
                                                        env1
                                                       in
                                                    Prims.op_Negation
                                                      uu____21974
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
                                                    let uu____22005 =
                                                      FStar_TypeChecker_Util.weaken_precondition
                                                        env1 c1 gf
                                                       in
                                                    let uu____22006 =
                                                      FStar_TypeChecker_Env.imp_guard
                                                        g g_when
                                                       in
                                                    (uu____22005,
                                                      uu____22006)
                                                | (FStar_Pervasives_Native.Some
                                                   f,FStar_Pervasives_Native.Some
                                                   w) ->
                                                    let g_f =
                                                      FStar_TypeChecker_Common.NonTrivial
                                                        f
                                                       in
                                                    let g_fw =
                                                      let uu____22027 =
                                                        FStar_Syntax_Util.mk_conj
                                                          f w
                                                         in
                                                      FStar_TypeChecker_Common.NonTrivial
                                                        uu____22027
                                                       in
                                                    let uu____22028 =
                                                      FStar_TypeChecker_Util.weaken_precondition
                                                        env1 c1 g_fw
                                                       in
                                                    let uu____22029 =
                                                      let uu____22030 =
                                                        FStar_TypeChecker_Env.guard_of_guard_formula
                                                          g_f
                                                         in
                                                      FStar_TypeChecker_Env.imp_guard
                                                        uu____22030 g_when
                                                       in
                                                    (uu____22028,
                                                      uu____22029)
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
                                                    let uu____22048 =
                                                      FStar_TypeChecker_Util.weaken_precondition
                                                        env1 c1 g_w
                                                       in
                                                    (uu____22048, g_when)
                                                 in
                                              (match uu____21940 with
                                               | (c_weak,g_when_weak) ->
                                                   let binders =
                                                     FStar_List.map
                                                       FStar_Syntax_Syntax.mk_binder
                                                       pat_bvs1
                                                      in
                                                   let maybe_return_c_weak
                                                     should_return1 =
                                                     let c_weak1 =
                                                       let uu____22091 =
                                                         should_return1 &&
                                                           (FStar_TypeChecker_Common.is_pure_or_ghost_lcomp
                                                              c_weak)
                                                          in
                                                       if uu____22091
                                                       then
                                                         FStar_TypeChecker_Util.maybe_assume_result_eq_pure_term
                                                           env branch_exp1
                                                           c_weak
                                                       else c_weak  in
                                                     let uu____22096 =
                                                       (let uu____22100 =
                                                          FStar_TypeChecker_Env.try_lookup_effect_lid
                                                            env
                                                            FStar_Parser_Const.effect_GTot_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____22100)
                                                         &&
                                                         (let uu____22104 =
                                                            FStar_All.pipe_right
                                                              c_weak1.FStar_TypeChecker_Common.eff_name
                                                              (FStar_TypeChecker_Env.norm_eff_name
                                                                 env)
                                                             in
                                                          FStar_All.pipe_right
                                                            uu____22104
                                                            (FStar_TypeChecker_Env.is_layered_effect
                                                               env))
                                                        in
                                                     if uu____22096
                                                     then
                                                       ((let uu____22108 =
                                                           FStar_All.pipe_left
                                                             (FStar_TypeChecker_Env.debug
                                                                env)
                                                             (FStar_Options.Other
                                                                "LayeredEffects")
                                                            in
                                                         if uu____22108
                                                         then
                                                           FStar_Util.print_string
                                                             "Typechecking pat_bv_tms ...\n"
                                                         else ());
                                                        (let pat_bv_tms1 =
                                                           FStar_List.fold_left2
                                                             (fun acc  ->
                                                                fun pat_bv_tm
                                                                   ->
                                                                  fun bv  ->
                                                                    let expected_t
                                                                    =
                                                                    let uu____22135
                                                                    =
                                                                    let uu____22144
                                                                    =
                                                                    FStar_Syntax_Syntax.null_binder
                                                                    pat_t  in
                                                                    [uu____22144]
                                                                     in
                                                                    let uu____22163
                                                                    =
                                                                    let uu____22166
                                                                    =
                                                                    let uu____22169
                                                                    =
                                                                    FStar_TypeChecker_Env.new_u_univ
                                                                    ()  in
                                                                    FStar_All.pipe_right
                                                                    uu____22169
                                                                    (fun
                                                                    _22172 
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    _22172)
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Total'
                                                                    bv.FStar_Syntax_Syntax.sort
                                                                    uu____22166
                                                                     in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu____22135
                                                                    uu____22163
                                                                     in
                                                                    let env1
                                                                    =
                                                                    let uu___2794_22174
                                                                    =
                                                                    FStar_TypeChecker_Env.set_expected_typ
                                                                    env
                                                                    expected_t
                                                                     in
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.is_pattern
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.is_pattern);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.use_eq);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.type_of
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.type_of);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.check_type_of
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.check_type_of);
                                                                    FStar_TypeChecker_Env.use_bv_sorts
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.use_bv_sorts);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.is_native_tactic
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.is_native_tactic);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (uu___2794_22174.FStar_TypeChecker_Env.erasable_types_tab)
                                                                    }  in
                                                                    let pat_bv_tm1
                                                                    =
                                                                    let uu____22177
                                                                    =
                                                                    tc_trivial_guard
                                                                    env1
                                                                    pat_bv_tm
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____22177
                                                                    FStar_Pervasives_Native.fst
                                                                     in
                                                                    FStar_List.append
                                                                    acc
                                                                    [pat_bv_tm1])
                                                             [] pat_bv_tms
                                                             pat_bvs1
                                                            in
                                                         let pat_bv_tms2 =
                                                           let uu____22189 =
                                                             FStar_All.pipe_right
                                                               pat_bv_tms1
                                                               (FStar_List.map
                                                                  (fun
                                                                    pat_bv_tm
                                                                     ->
                                                                    let uu____22201
                                                                    =
                                                                    let uu____22206
                                                                    =
                                                                    let uu____22207
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    scrutinee_tm
                                                                    FStar_Syntax_Syntax.as_arg
                                                                     in
                                                                    [uu____22207]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    pat_bv_tm
                                                                    uu____22206
                                                                     in
                                                                    uu____22201
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Range.dummyRange))
                                                              in
                                                           FStar_All.pipe_right
                                                             uu____22189
                                                             (FStar_List.map
                                                                (FStar_TypeChecker_Normalize.normalize
                                                                   [FStar_TypeChecker_Env.Beta]
                                                                   env))
                                                            in
                                                         (let uu____22245 =
                                                            FStar_All.pipe_left
                                                              (FStar_TypeChecker_Env.debug
                                                                 env)
                                                              (FStar_Options.Other
                                                                 "LayeredEffects")
                                                             in
                                                          if uu____22245
                                                          then
                                                            let uu____22250 =
                                                              FStar_List.fold_left
                                                                (fun s  ->
                                                                   fun t  ->
                                                                    let uu____22259
                                                                    =
                                                                    let uu____22261
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    t  in
                                                                    Prims.op_Hat
                                                                    ";"
                                                                    uu____22261
                                                                     in
                                                                    Prims.op_Hat
                                                                    s
                                                                    uu____22259)
                                                                ""
                                                                pat_bv_tms2
                                                               in
                                                            FStar_Util.print1
                                                              "tc_eqn: typechecked pat_bv_tms %s"
                                                              uu____22250
                                                          else ());
                                                         FStar_TypeChecker_Util.close_layered_lcomp
                                                           env pat_bvs1
                                                           pat_bv_tms2
                                                           c_weak1))
                                                     else
                                                       FStar_TypeChecker_Util.close_wp_lcomp
                                                         env pat_bvs1 c_weak1
                                                      in
                                                   ((let uu____22271 =
                                                       (let uu____22275 =
                                                          FStar_TypeChecker_Env.try_lookup_effect_lid
                                                            env
                                                            FStar_Parser_Const.effect_GTot_lid
                                                           in
                                                        FStar_Option.isSome
                                                          uu____22275)
                                                         &&
                                                         (FStar_All.pipe_left
                                                            (FStar_TypeChecker_Env.debug
                                                               env)
                                                            (FStar_Options.Other
                                                               "LayeredEffects"))
                                                        in
                                                     if uu____22271
                                                     then
                                                       let uu____22281 =
                                                         let uu____22283 =
                                                           maybe_return_c_weak
                                                             false
                                                            in
                                                         FStar_TypeChecker_Common.lcomp_to_string
                                                           uu____22283
                                                          in
                                                       FStar_Util.print1
                                                         "tc_eqn: c_weak applied to false: %s\n"
                                                         uu____22281
                                                     else ());
                                                    (let uu____22288 =
                                                       FStar_TypeChecker_Env.close_guard
                                                         env binders
                                                         g_when_weak
                                                        in
                                                     let uu____22289 =
                                                       FStar_TypeChecker_Env.conj_guard
                                                         guard_pat g_branch1
                                                        in
                                                     ((c_weak.FStar_TypeChecker_Common.eff_name),
                                                       (c_weak.FStar_TypeChecker_Common.cflags),
                                                       maybe_return_c_weak,
                                                       uu____22288,
                                                       uu____22289))))
                                           in
                                        match uu____21845 with
                                        | (effect_label,cflags,maybe_return_c,g_when1,g_branch1)
                                            ->
                                            let branch_guard =
                                              let uu____22343 =
                                                let uu____22345 =
                                                  FStar_TypeChecker_Env.should_verify
                                                    env
                                                   in
                                                Prims.op_Negation uu____22345
                                                 in
                                              if uu____22343
                                              then FStar_Syntax_Util.t_true
                                              else
                                                (let rec build_branch_guard
                                                   scrutinee_tm1 pattern2
                                                   pat_exp1 =
                                                   let discriminate
                                                     scrutinee_tm2 f =
                                                     let uu____22399 =
                                                       let uu____22407 =
                                                         FStar_TypeChecker_Env.typ_of_datacon
                                                           env
                                                           f.FStar_Syntax_Syntax.v
                                                          in
                                                       FStar_TypeChecker_Env.datacons_of_typ
                                                         env uu____22407
                                                        in
                                                     match uu____22399 with
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
                                                           let discriminator
                                                             =
                                                             FStar_Syntax_Util.mk_discriminator
                                                               f.FStar_Syntax_Syntax.v
                                                              in
                                                           let uu____22423 =
                                                             FStar_TypeChecker_Env.try_lookup_lid
                                                               env
                                                               discriminator
                                                              in
                                                           (match uu____22423
                                                            with
                                                            | FStar_Pervasives_Native.None
                                                                 -> []
                                                            | uu____22444 ->
                                                                let disc =
                                                                  FStar_Syntax_Syntax.fvar
                                                                    discriminator
                                                                    (
                                                                    FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                   in
                                                                let disc1 =
                                                                  let uu____22460
                                                                    =
                                                                    let uu____22465
                                                                    =
                                                                    let uu____22466
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    scrutinee_tm2
                                                                     in
                                                                    [uu____22466]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    disc
                                                                    uu____22465
                                                                     in
                                                                  uu____22460
                                                                    FStar_Pervasives_Native.None
                                                                    scrutinee_tm2.FStar_Syntax_Syntax.pos
                                                                   in
                                                                let uu____22491
                                                                  =
                                                                  FStar_Syntax_Util.mk_eq2
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    FStar_Syntax_Util.t_bool
                                                                    disc1
                                                                    FStar_Syntax_Util.exp_true_bool
                                                                   in
                                                                [uu____22491])
                                                         else []
                                                      in
                                                   let fail1 uu____22499 =
                                                     let uu____22500 =
                                                       let uu____22502 =
                                                         FStar_Range.string_of_range
                                                           pat_exp1.FStar_Syntax_Syntax.pos
                                                          in
                                                       let uu____22504 =
                                                         FStar_Syntax_Print.term_to_string
                                                           pat_exp1
                                                          in
                                                       let uu____22506 =
                                                         FStar_Syntax_Print.tag_of_term
                                                           pat_exp1
                                                          in
                                                       FStar_Util.format3
                                                         "tc_eqn: Impossible (%s) %s (%s)"
                                                         uu____22502
                                                         uu____22504
                                                         uu____22506
                                                        in
                                                     failwith uu____22500  in
                                                   let rec head_constructor t
                                                     =
                                                     match t.FStar_Syntax_Syntax.n
                                                     with
                                                     | FStar_Syntax_Syntax.Tm_fvar
                                                         fv ->
                                                         fv.FStar_Syntax_Syntax.fv_name
                                                     | FStar_Syntax_Syntax.Tm_uinst
                                                         (t1,uu____22521) ->
                                                         head_constructor t1
                                                     | uu____22526 ->
                                                         fail1 ()
                                                      in
                                                   let force_scrutinee
                                                     uu____22532 =
                                                     match scrutinee_tm1 with
                                                     | FStar_Pervasives_Native.None
                                                          ->
                                                         let uu____22533 =
                                                           let uu____22535 =
                                                             FStar_Range.string_of_range
                                                               pattern2.FStar_Syntax_Syntax.p
                                                              in
                                                           let uu____22537 =
                                                             FStar_Syntax_Print.pat_to_string
                                                               pattern2
                                                              in
                                                           FStar_Util.format2
                                                             "Impossible (%s): scrutinee of match is not defined %s"
                                                             uu____22535
                                                             uu____22537
                                                            in
                                                         failwith uu____22533
                                                     | FStar_Pervasives_Native.Some
                                                         t -> t
                                                      in
                                                   let pat_exp2 =
                                                     let uu____22544 =
                                                       FStar_Syntax_Subst.compress
                                                         pat_exp1
                                                        in
                                                     FStar_All.pipe_right
                                                       uu____22544
                                                       FStar_Syntax_Util.unmeta
                                                      in
                                                   match ((pattern2.FStar_Syntax_Syntax.v),
                                                           (pat_exp2.FStar_Syntax_Syntax.n))
                                                   with
                                                   | (uu____22549,FStar_Syntax_Syntax.Tm_name
                                                      uu____22550) -> []
                                                   | (uu____22551,FStar_Syntax_Syntax.Tm_constant
                                                      (FStar_Const.Const_unit
                                                      )) -> []
                                                   | (FStar_Syntax_Syntax.Pat_constant
                                                      _c,FStar_Syntax_Syntax.Tm_constant
                                                      c1) ->
                                                       let uu____22554 =
                                                         let uu____22555 =
                                                           tc_constant env
                                                             pat_exp2.FStar_Syntax_Syntax.pos
                                                             c1
                                                            in
                                                         let uu____22556 =
                                                           force_scrutinee ()
                                                            in
                                                         FStar_Syntax_Util.mk_eq2
                                                           FStar_Syntax_Syntax.U_zero
                                                           uu____22555
                                                           uu____22556
                                                           pat_exp2
                                                          in
                                                       [uu____22554]
                                                   | (FStar_Syntax_Syntax.Pat_constant
                                                      (FStar_Const.Const_int
                                                      (uu____22557,FStar_Pervasives_Native.Some
                                                       uu____22558)),uu____22559)
                                                       ->
                                                       let uu____22576 =
                                                         let uu____22583 =
                                                           FStar_TypeChecker_Env.clear_expected_typ
                                                             env
                                                            in
                                                         match uu____22583
                                                         with
                                                         | (env1,uu____22597)
                                                             ->
                                                             env1.FStar_TypeChecker_Env.type_of
                                                               env1 pat_exp2
                                                          in
                                                       (match uu____22576
                                                        with
                                                        | (uu____22604,t,uu____22606)
                                                            ->
                                                            let uu____22607 =
                                                              let uu____22608
                                                                =
                                                                force_scrutinee
                                                                  ()
                                                                 in
                                                              FStar_Syntax_Util.mk_eq2
                                                                FStar_Syntax_Syntax.U_zero
                                                                t uu____22608
                                                                pat_exp2
                                                               in
                                                            [uu____22607])
                                                   | (FStar_Syntax_Syntax.Pat_cons
                                                      (uu____22609,[]),FStar_Syntax_Syntax.Tm_uinst
                                                      uu____22610) ->
                                                       let f =
                                                         head_constructor
                                                           pat_exp2
                                                          in
                                                       let uu____22634 =
                                                         let uu____22636 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____22636
                                                          in
                                                       if uu____22634
                                                       then
                                                         failwith
                                                           "Impossible: nullary patterns must be data constructors"
                                                       else
                                                         (let uu____22646 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          let uu____22649 =
                                                            head_constructor
                                                              pat_exp2
                                                             in
                                                          discriminate
                                                            uu____22646
                                                            uu____22649)
                                                   | (FStar_Syntax_Syntax.Pat_cons
                                                      (uu____22652,[]),FStar_Syntax_Syntax.Tm_fvar
                                                      uu____22653) ->
                                                       let f =
                                                         head_constructor
                                                           pat_exp2
                                                          in
                                                       let uu____22671 =
                                                         let uu____22673 =
                                                           FStar_TypeChecker_Env.is_datacon
                                                             env
                                                             f.FStar_Syntax_Syntax.v
                                                            in
                                                         Prims.op_Negation
                                                           uu____22673
                                                          in
                                                       if uu____22671
                                                       then
                                                         failwith
                                                           "Impossible: nullary patterns must be data constructors"
                                                       else
                                                         (let uu____22683 =
                                                            force_scrutinee
                                                              ()
                                                             in
                                                          let uu____22686 =
                                                            head_constructor
                                                              pat_exp2
                                                             in
                                                          discriminate
                                                            uu____22683
                                                            uu____22686)
                                                   | (FStar_Syntax_Syntax.Pat_cons
                                                      (uu____22689,pat_args),FStar_Syntax_Syntax.Tm_app
                                                      (head1,args)) ->
                                                       let f =
                                                         head_constructor
                                                           head1
                                                          in
                                                       let uu____22736 =
                                                         (let uu____22740 =
                                                            FStar_TypeChecker_Env.is_datacon
                                                              env
                                                              f.FStar_Syntax_Syntax.v
                                                             in
                                                          Prims.op_Negation
                                                            uu____22740)
                                                           ||
                                                           ((FStar_List.length
                                                               pat_args)
                                                              <>
                                                              (FStar_List.length
                                                                 args))
                                                          in
                                                       if uu____22736
                                                       then
                                                         failwith
                                                           "Impossible: application patterns must be fully-applied data constructors"
                                                       else
                                                         (let sub_term_guards
                                                            =
                                                            let uu____22768 =
                                                              let uu____22773
                                                                =
                                                                FStar_List.zip
                                                                  pat_args
                                                                  args
                                                                 in
                                                              FStar_All.pipe_right
                                                                uu____22773
                                                                (FStar_List.mapi
                                                                   (fun i  ->
                                                                    fun
                                                                    uu____22859
                                                                     ->
                                                                    match uu____22859
                                                                    with
                                                                    | 
                                                                    ((pi,uu____22881),
                                                                    (ei,uu____22883))
                                                                    ->
                                                                    let projector
                                                                    =
                                                                    FStar_TypeChecker_Env.lookup_projector
                                                                    env
                                                                    f.FStar_Syntax_Syntax.v
                                                                    i  in
                                                                    let scrutinee_tm2
                                                                    =
                                                                    let uu____22911
                                                                    =
                                                                    FStar_TypeChecker_Env.try_lookup_lid
                                                                    env
                                                                    projector
                                                                     in
                                                                    match uu____22911
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                     ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu____22932
                                                                    ->
                                                                    let proj
                                                                    =
                                                                    let uu____22944
                                                                    =
                                                                    FStar_Ident.set_lid_range
                                                                    projector
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Syntax_Syntax.fvar
                                                                    uu____22944
                                                                    (FStar_Syntax_Syntax.Delta_equational_at_level
                                                                    Prims.int_one)
                                                                    FStar_Pervasives_Native.None
                                                                     in
                                                                    let uu____22946
                                                                    =
                                                                    let uu____22947
                                                                    =
                                                                    let uu____22952
                                                                    =
                                                                    let uu____22953
                                                                    =
                                                                    let uu____22962
                                                                    =
                                                                    force_scrutinee
                                                                    ()  in
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    uu____22962
                                                                     in
                                                                    [uu____22953]
                                                                     in
                                                                    FStar_Syntax_Syntax.mk_Tm_app
                                                                    proj
                                                                    uu____22952
                                                                     in
                                                                    uu____22947
                                                                    FStar_Pervasives_Native.None
                                                                    f.FStar_Syntax_Syntax.p
                                                                     in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu____22946
                                                                     in
                                                                    build_branch_guard
                                                                    scrutinee_tm2
                                                                    pi ei))
                                                               in
                                                            FStar_All.pipe_right
                                                              uu____22768
                                                              FStar_List.flatten
                                                             in
                                                          let uu____22985 =
                                                            let uu____22988 =
                                                              force_scrutinee
                                                                ()
                                                               in
                                                            discriminate
                                                              uu____22988 f
                                                             in
                                                          FStar_List.append
                                                            uu____22985
                                                            sub_term_guards)
                                                   | (FStar_Syntax_Syntax.Pat_dot_term
                                                      uu____22991,uu____22992)
                                                       -> []
                                                   | uu____22999 ->
                                                       let uu____23004 =
                                                         let uu____23006 =
                                                           FStar_Syntax_Print.pat_to_string
                                                             pattern2
                                                            in
                                                         let uu____23008 =
                                                           FStar_Syntax_Print.term_to_string
                                                             pat_exp2
                                                            in
                                                         FStar_Util.format2
                                                           "Internal error: unexpected elaborated pattern: %s and pattern expression %s"
                                                           uu____23006
                                                           uu____23008
                                                          in
                                                       failwith uu____23004
                                                    in
                                                 let build_and_check_branch_guard
                                                   scrutinee_tm1 pattern2 pat
                                                   =
                                                   let uu____23037 =
                                                     let uu____23039 =
                                                       FStar_TypeChecker_Env.should_verify
                                                         env
                                                        in
                                                     Prims.op_Negation
                                                       uu____23039
                                                      in
                                                   if uu____23037
                                                   then
                                                     FStar_TypeChecker_Util.fvar_const
                                                       env
                                                       FStar_Parser_Const.true_lid
                                                   else
                                                     (let t =
                                                        let uu____23045 =
                                                          build_branch_guard
                                                            scrutinee_tm1
                                                            pattern2 pat
                                                           in
                                                        FStar_All.pipe_left
                                                          FStar_Syntax_Util.mk_conj_l
                                                          uu____23045
                                                         in
                                                      let uu____23054 =
                                                        FStar_Syntax_Util.type_u
                                                          ()
                                                         in
                                                      match uu____23054 with
                                                      | (k,uu____23060) ->
                                                          let uu____23061 =
                                                            tc_check_tot_or_gtot_term
                                                              scrutinee_env t
                                                              k
                                                             in
                                                          (match uu____23061
                                                           with
                                                           | (t1,uu____23069,uu____23070)
                                                               -> t1))
                                                    in
                                                 let branch_guard =
                                                   build_and_check_branch_guard
                                                     (FStar_Pervasives_Native.Some
                                                        scrutinee_tm)
                                                     pattern1 norm_pat_exp
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
                                            ((let uu____23082 =
                                                FStar_TypeChecker_Env.debug
                                                  env FStar_Options.High
                                                 in
                                              if uu____23082
                                              then
                                                let uu____23085 =
                                                  FStar_TypeChecker_Rel.guard_to_string
                                                    env guard
                                                   in
                                                FStar_All.pipe_left
                                                  (FStar_Util.print1
                                                     "Carrying guard from match: %s\n")
                                                  uu____23085
                                              else ());
                                             (let uu____23091 =
                                                FStar_Syntax_Subst.close_branch
                                                  (pattern1, when_clause1,
                                                    branch_exp1)
                                                 in
                                              let uu____23108 =
                                                let uu____23109 =
                                                  FStar_List.map
                                                    FStar_Syntax_Syntax.mk_binder
                                                    pat_bvs1
                                                   in
                                                FStar_TypeChecker_Util.close_guard_implicits
                                                  env uu____23109 guard
                                                 in
                                              (uu____23091, branch_guard,
                                                effect_label, cflags,
                                                maybe_return_c, uu____23108,
                                                erasable1)))))))))))

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
          let uu____23157 = check_let_bound_def true env1 lb  in
          (match uu____23157 with
           | (e1,univ_vars1,c1,g1,annotated) ->
               let uu____23183 =
                 if
                   annotated &&
                     (Prims.op_Negation env1.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____23205 =
                     FStar_TypeChecker_Normalize.reduce_uvar_solutions env1
                       e1
                      in
                   (g1, uu____23205, univ_vars1, c1)
                 else
                   (let g11 =
                      let uu____23211 =
                        FStar_TypeChecker_Rel.solve_deferred_constraints env1
                          g1
                         in
                      FStar_All.pipe_right uu____23211
                        (FStar_TypeChecker_Rel.resolve_implicits env1)
                       in
                    let uu____23212 = FStar_TypeChecker_Common.lcomp_comp c1
                       in
                    match uu____23212 with
                    | (comp1,g_comp1) ->
                        let g12 =
                          FStar_TypeChecker_Env.conj_guard g11 g_comp1  in
                        let uu____23230 =
                          let uu____23243 =
                            FStar_TypeChecker_Util.generalize env1 false
                              [((lb.FStar_Syntax_Syntax.lbname), e1, comp1)]
                             in
                          FStar_List.hd uu____23243  in
                        (match uu____23230 with
                         | (uu____23293,univs1,e11,c11,gvs) ->
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
                             let uu____23307 =
                               FStar_TypeChecker_Common.lcomp_of_comp c11  in
                             (g14, e11, univs1, uu____23307)))
                  in
               (match uu____23183 with
                | (g11,e11,univ_vars2,c11) ->
                    let uu____23324 =
                      let uu____23333 =
                        FStar_TypeChecker_Env.should_verify env1  in
                      if uu____23333
                      then
                        let uu____23344 =
                          FStar_TypeChecker_Util.check_top_level env1 g11 c11
                           in
                        match uu____23344 with
                        | (ok,c12) ->
                            (if ok
                             then (e2, c12)
                             else
                               ((let uu____23378 =
                                   FStar_TypeChecker_Env.get_range env1  in
                                 FStar_Errors.log_issue uu____23378
                                   FStar_TypeChecker_Err.top_level_effect);
                                (let uu____23379 =
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_meta
                                        (e2,
                                          (FStar_Syntax_Syntax.Meta_desugared
                                             FStar_Syntax_Syntax.Masked_effect)))
                                     FStar_Pervasives_Native.None
                                     e2.FStar_Syntax_Syntax.pos
                                    in
                                 (uu____23379, c12))))
                      else
                        (FStar_TypeChecker_Rel.force_trivial_guard env1 g11;
                         (let uu____23391 =
                            FStar_TypeChecker_Common.lcomp_comp c11  in
                          match uu____23391 with
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
                                  let uu____23415 =
                                    FStar_Syntax_Util.is_pure_comp c  in
                                  if uu____23415
                                  then e2
                                  else
                                    ((let uu____23423 =
                                        FStar_TypeChecker_Env.get_range env1
                                         in
                                      FStar_Errors.log_issue uu____23423
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
                    (match uu____23324 with
                     | (e21,c12) ->
                         ((let uu____23447 =
                             FStar_TypeChecker_Env.debug env1
                               FStar_Options.Medium
                              in
                           if uu____23447
                           then
                             let uu____23450 =
                               FStar_Syntax_Print.term_to_string e11  in
                             FStar_Util.print1
                               "Let binding BEFORE tcnorm: %s\n" uu____23450
                           else ());
                          (let e12 =
                             let uu____23456 = FStar_Options.tcnorm ()  in
                             if uu____23456
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
                           (let uu____23462 =
                              FStar_TypeChecker_Env.debug env1
                                FStar_Options.Medium
                               in
                            if uu____23462
                            then
                              let uu____23465 =
                                FStar_Syntax_Print.term_to_string e12  in
                              FStar_Util.print1
                                "Let binding AFTER tcnorm: %s\n" uu____23465
                            else ());
                           (let cres =
                              let uu____23471 =
                                FStar_Syntax_Util.is_pure_or_ghost_comp c12
                                 in
                              if uu____23471
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
                                   | (wp,uu____23479)::[] -> wp
                                   | uu____23504 ->
                                       failwith
                                         "Impossible! check_top_level_let: got unexpected effect args"
                                    in
                                 let c1_eff_decl =
                                   FStar_TypeChecker_Env.get_effect_decl env1
                                     c1_comp_typ.FStar_Syntax_Syntax.effect_name
                                    in
                                 let wp2 =
                                   let uu____23520 =
                                     let uu____23525 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         [FStar_Syntax_Syntax.U_zero] env1
                                         c1_eff_decl
                                         c1_eff_decl.FStar_Syntax_Syntax.ret_wp
                                        in
                                     let uu____23526 =
                                       let uu____23527 =
                                         FStar_Syntax_Syntax.as_arg
                                           FStar_Syntax_Syntax.t_unit
                                          in
                                       let uu____23536 =
                                         let uu____23547 =
                                           FStar_Syntax_Syntax.as_arg
                                             FStar_Syntax_Syntax.unit_const
                                            in
                                         [uu____23547]  in
                                       uu____23527 :: uu____23536  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____23525 uu____23526
                                      in
                                   uu____23520 FStar_Pervasives_Native.None
                                     e21.FStar_Syntax_Syntax.pos
                                    in
                                 let wp =
                                   let uu____23583 =
                                     let uu____23588 =
                                       FStar_TypeChecker_Env.inst_effect_fun_with
                                         (FStar_List.append
                                            c1_comp_typ.FStar_Syntax_Syntax.comp_univs
                                            [FStar_Syntax_Syntax.U_zero])
                                         env1 c1_eff_decl
                                         c1_eff_decl.FStar_Syntax_Syntax.bind_wp
                                        in
                                     let uu____23589 =
                                       let uu____23590 =
                                         let uu____23599 =
                                           FStar_Syntax_Syntax.mk
                                             (FStar_Syntax_Syntax.Tm_constant
                                                (FStar_Const.Const_range
                                                   (lb.FStar_Syntax_Syntax.lbpos)))
                                             FStar_Pervasives_Native.None
                                             lb.FStar_Syntax_Syntax.lbpos
                                            in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____23599
                                          in
                                       let uu____23608 =
                                         let uu____23619 =
                                           FStar_All.pipe_left
                                             FStar_Syntax_Syntax.as_arg
                                             c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                            in
                                         let uu____23636 =
                                           let uu____23647 =
                                             FStar_Syntax_Syntax.as_arg
                                               FStar_Syntax_Syntax.t_unit
                                              in
                                           let uu____23656 =
                                             let uu____23667 =
                                               FStar_Syntax_Syntax.as_arg
                                                 c1_wp
                                                in
                                             let uu____23676 =
                                               let uu____23687 =
                                                 let uu____23696 =
                                                   let uu____23697 =
                                                     let uu____23698 =
                                                       FStar_Syntax_Syntax.null_binder
                                                         c1_comp_typ.FStar_Syntax_Syntax.result_typ
                                                        in
                                                     [uu____23698]  in
                                                   FStar_Syntax_Util.abs
                                                     uu____23697 wp2
                                                     (FStar_Pervasives_Native.Some
                                                        (FStar_Syntax_Util.mk_residual_comp
                                                           FStar_Parser_Const.effect_Tot_lid
                                                           FStar_Pervasives_Native.None
                                                           [FStar_Syntax_Syntax.TOTAL]))
                                                    in
                                                 FStar_All.pipe_left
                                                   FStar_Syntax_Syntax.as_arg
                                                   uu____23696
                                                  in
                                               [uu____23687]  in
                                             uu____23667 :: uu____23676  in
                                           uu____23647 :: uu____23656  in
                                         uu____23619 :: uu____23636  in
                                       uu____23590 :: uu____23608  in
                                     FStar_Syntax_Syntax.mk_Tm_app
                                       uu____23588 uu____23589
                                      in
                                   uu____23583 FStar_Pervasives_Native.None
                                     lb.FStar_Syntax_Syntax.lbpos
                                    in
                                 let uu____23775 =
                                   let uu____23776 =
                                     let uu____23787 =
                                       FStar_Syntax_Syntax.as_arg wp  in
                                     [uu____23787]  in
                                   {
                                     FStar_Syntax_Syntax.comp_univs =
                                       [FStar_Syntax_Syntax.U_zero];
                                     FStar_Syntax_Syntax.effect_name =
                                       (c1_comp_typ.FStar_Syntax_Syntax.effect_name);
                                     FStar_Syntax_Syntax.result_typ =
                                       FStar_Syntax_Syntax.t_unit;
                                     FStar_Syntax_Syntax.effect_args =
                                       uu____23776;
                                     FStar_Syntax_Syntax.flags = []
                                   }  in
                                 FStar_Syntax_Syntax.mk_Comp uu____23775)
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
                            let uu____23815 =
                              FStar_Syntax_Syntax.mk
                                (FStar_Syntax_Syntax.Tm_let
                                   ((false, [lb1]), e21))
                                FStar_Pervasives_Native.None
                                e.FStar_Syntax_Syntax.pos
                               in
                            let uu____23829 =
                              FStar_TypeChecker_Common.lcomp_of_comp cres  in
                            (uu____23815, uu____23829,
                              FStar_TypeChecker_Env.trivial_guard)))))))
      | uu____23830 -> failwith "Impossible"

and (maybe_intro_smt_lemma :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_TypeChecker_Common.lcomp -> FStar_TypeChecker_Common.lcomp)
  =
  fun env  ->
    fun lem_typ  ->
      fun c2  ->
        let uu____23841 = FStar_Syntax_Util.is_smt_lemma lem_typ  in
        if uu____23841
        then
          let universe_of_binders bs =
            let uu____23868 =
              FStar_List.fold_left
                (fun uu____23893  ->
                   fun b  ->
                     match uu____23893 with
                     | (env1,us) ->
                         let u =
                           env1.FStar_TypeChecker_Env.universe_of env1
                             (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                            in
                         let env2 =
                           FStar_TypeChecker_Env.push_binders env1 [b]  in
                         (env2, (u :: us))) (env, []) bs
               in
            match uu____23868 with | (uu____23941,us) -> FStar_List.rev us
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
            let uu___3042_23977 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3042_23977.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3042_23977.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3042_23977.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3042_23977.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3042_23977.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3042_23977.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3042_23977.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3042_23977.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3042_23977.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3042_23977.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3042_23977.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3042_23977.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3042_23977.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3042_23977.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3042_23977.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level = false;
              FStar_TypeChecker_Env.check_uvars =
                (uu___3042_23977.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3042_23977.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3042_23977.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3042_23977.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3042_23977.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3042_23977.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3042_23977.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3042_23977.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3042_23977.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3042_23977.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3042_23977.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3042_23977.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3042_23977.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3042_23977.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts =
                (uu___3042_23977.FStar_TypeChecker_Env.use_bv_sorts);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3042_23977.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3042_23977.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3042_23977.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3042_23977.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3042_23977.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3042_23977.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3042_23977.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3042_23977.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3042_23977.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3042_23977.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3042_23977.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3042_23977.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3042_23977.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3042_23977.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3042_23977.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let uu____23979 =
            let uu____23991 =
              let uu____23992 = FStar_TypeChecker_Env.clear_expected_typ env2
                 in
              FStar_All.pipe_right uu____23992 FStar_Pervasives_Native.fst
               in
            check_let_bound_def false uu____23991 lb  in
          (match uu____23979 with
           | (e1,uu____24015,c1,g1,annotated) ->
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
                  (let uu____24029 =
                     let uu____24035 =
                       let uu____24037 = FStar_Syntax_Print.term_to_string e1
                          in
                       let uu____24039 =
                         FStar_Syntax_Print.lid_to_string
                           c1.FStar_TypeChecker_Common.eff_name
                          in
                       FStar_Util.format2
                         "Definitions marked @inline_let are expected to be pure or ghost; got an expression \"%s\" with effect \"%s\""
                         uu____24037 uu____24039
                        in
                     (FStar_Errors.Fatal_ExpectedPureExpression, uu____24035)
                      in
                   FStar_Errors.raise_error uu____24029
                     e1.FStar_Syntax_Syntax.pos)
                else ();
                (let attrs =
                   let uu____24050 =
                     (pure_or_ghost && (Prims.op_Negation is_inline_let)) &&
                       (FStar_Syntax_Util.is_unit
                          c1.FStar_TypeChecker_Common.res_typ)
                      in
                   if uu____24050
                   then FStar_Syntax_Util.inline_let_attr ::
                     (lb.FStar_Syntax_Syntax.lbattrs)
                   else lb.FStar_Syntax_Syntax.lbattrs  in
                 let x =
                   let uu___3057_24062 =
                     FStar_Util.left lb.FStar_Syntax_Syntax.lbname  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___3057_24062.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___3057_24062.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort =
                       (c1.FStar_TypeChecker_Common.res_typ)
                   }  in
                 let uu____24063 =
                   let uu____24068 =
                     let uu____24069 = FStar_Syntax_Syntax.mk_binder x  in
                     [uu____24069]  in
                   FStar_Syntax_Subst.open_term uu____24068 e2  in
                 match uu____24063 with
                 | (xb,e21) ->
                     let xbinder = FStar_List.hd xb  in
                     let x1 = FStar_Pervasives_Native.fst xbinder  in
                     let env_x = FStar_TypeChecker_Env.push_bv env2 x1  in
                     let uu____24113 = tc_term env_x e21  in
                     (match uu____24113 with
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
                            let uu____24139 =
                              let uu____24146 =
                                let uu____24147 =
                                  let uu____24161 =
                                    FStar_Syntax_Subst.close xb e23  in
                                  ((false, [lb1]), uu____24161)  in
                                FStar_Syntax_Syntax.Tm_let uu____24147  in
                              FStar_Syntax_Syntax.mk uu____24146  in
                            uu____24139 FStar_Pervasives_Native.None
                              e.FStar_Syntax_Syntax.pos
                             in
                          let e4 =
                            FStar_TypeChecker_Util.maybe_monadic env2 e3
                              cres.FStar_TypeChecker_Common.eff_name
                              cres.FStar_TypeChecker_Common.res_typ
                             in
                          let x_eq_e1 =
                            let uu____24179 =
                              let uu____24180 =
                                env2.FStar_TypeChecker_Env.universe_of env2
                                  c1.FStar_TypeChecker_Common.res_typ
                                 in
                              let uu____24181 =
                                FStar_Syntax_Syntax.bv_to_name x1  in
                              FStar_Syntax_Util.mk_eq2 uu____24180
                                c1.FStar_TypeChecker_Common.res_typ
                                uu____24181 e11
                               in
                            FStar_All.pipe_left
                              (fun _24182  ->
                                 FStar_TypeChecker_Common.NonTrivial _24182)
                              uu____24179
                             in
                          let g21 =
                            let uu____24184 =
                              let uu____24185 =
                                FStar_TypeChecker_Env.guard_of_guard_formula
                                  x_eq_e1
                                 in
                              FStar_TypeChecker_Env.imp_guard uu____24185 g2
                               in
                            FStar_TypeChecker_Env.close_guard env2 xb
                              uu____24184
                             in
                          let g22 =
                            FStar_TypeChecker_Util.close_guard_implicits env2
                              xb g21
                             in
                          let guard = FStar_TypeChecker_Env.conj_guard g1 g22
                             in
                          let uu____24188 =
                            let uu____24190 =
                              FStar_TypeChecker_Env.expected_typ env2  in
                            FStar_Option.isSome uu____24190  in
                          if uu____24188
                          then
                            let tt =
                              let uu____24201 =
                                FStar_TypeChecker_Env.expected_typ env2  in
                              FStar_All.pipe_right uu____24201
                                FStar_Option.get
                               in
                            ((let uu____24207 =
                                FStar_All.pipe_left
                                  (FStar_TypeChecker_Env.debug env2)
                                  (FStar_Options.Other "Exports")
                                 in
                              if uu____24207
                              then
                                let uu____24212 =
                                  FStar_Syntax_Print.term_to_string tt  in
                                let uu____24214 =
                                  FStar_Syntax_Print.term_to_string
                                    cres.FStar_TypeChecker_Common.res_typ
                                   in
                                FStar_Util.print2
                                  "Got expected type from env %s\ncres.res_typ=%s\n"
                                  uu____24212 uu____24214
                              else ());
                             (e4, cres, guard))
                          else
                            (let uu____24221 =
                               check_no_escape FStar_Pervasives_Native.None
                                 env2 [x1]
                                 cres.FStar_TypeChecker_Common.res_typ
                                in
                             match uu____24221 with
                             | (t,g_ex) ->
                                 ((let uu____24235 =
                                     FStar_All.pipe_left
                                       (FStar_TypeChecker_Env.debug env2)
                                       (FStar_Options.Other "Exports")
                                      in
                                   if uu____24235
                                   then
                                     let uu____24240 =
                                       FStar_Syntax_Print.term_to_string
                                         cres.FStar_TypeChecker_Common.res_typ
                                        in
                                     let uu____24242 =
                                       FStar_Syntax_Print.term_to_string t
                                        in
                                     FStar_Util.print2
                                       "Checked %s has no escaping types; normalized to %s\n"
                                       uu____24240 uu____24242
                                   else ());
                                  (let uu____24247 =
                                     FStar_TypeChecker_Env.conj_guard g_ex
                                       guard
                                      in
                                   (e4,
                                     (let uu___3090_24249 = cres  in
                                      {
                                        FStar_TypeChecker_Common.eff_name =
                                          (uu___3090_24249.FStar_TypeChecker_Common.eff_name);
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          (uu___3090_24249.FStar_TypeChecker_Common.cflags);
                                        FStar_TypeChecker_Common.comp_thunk =
                                          (uu___3090_24249.FStar_TypeChecker_Common.comp_thunk)
                                      }), uu____24247))))))))
      | uu____24250 ->
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
          let uu____24286 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____24286 with
           | (lbs1,e21) ->
               let uu____24305 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____24305 with
                | (env0,topt) ->
                    let uu____24324 = build_let_rec_env true env0 lbs1  in
                    (match uu____24324 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____24347 = check_let_recs rec_env lbs2  in
                         (match uu____24347 with
                          | (lbs3,g_lbs) ->
                              let g_lbs1 =
                                let uu____24367 =
                                  let uu____24368 =
                                    FStar_TypeChecker_Env.conj_guard g_t
                                      g_lbs
                                     in
                                  FStar_All.pipe_right uu____24368
                                    (FStar_TypeChecker_Rel.solve_deferred_constraints
                                       env1)
                                   in
                                FStar_All.pipe_right uu____24367
                                  (FStar_TypeChecker_Rel.resolve_implicits
                                     env1)
                                 in
                              let all_lb_names =
                                let uu____24374 =
                                  FStar_All.pipe_right lbs3
                                    (FStar_List.map
                                       (fun lb  ->
                                          FStar_Util.right
                                            lb.FStar_Syntax_Syntax.lbname))
                                   in
                                FStar_All.pipe_right uu____24374
                                  (fun _24391  ->
                                     FStar_Pervasives_Native.Some _24391)
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
                                     let uu____24428 =
                                       FStar_All.pipe_right lbs3
                                         (FStar_List.map
                                            (fun lb  ->
                                               let uu____24462 =
                                                 FStar_Syntax_Syntax.mk_Total
                                                   lb.FStar_Syntax_Syntax.lbtyp
                                                  in
                                               ((lb.FStar_Syntax_Syntax.lbname),
                                                 (lb.FStar_Syntax_Syntax.lbdef),
                                                 uu____24462)))
                                        in
                                     FStar_TypeChecker_Util.generalize env1
                                       true uu____24428
                                      in
                                   FStar_List.map2
                                     (fun uu____24497  ->
                                        fun lb  ->
                                          match uu____24497 with
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
                                let uu____24545 =
                                  FStar_Syntax_Syntax.mk_Total
                                    FStar_Syntax_Syntax.t_unit
                                   in
                                FStar_All.pipe_left
                                  FStar_TypeChecker_Common.lcomp_of_comp
                                  uu____24545
                                 in
                              let uu____24546 =
                                FStar_Syntax_Subst.close_let_rec lbs4 e21  in
                              (match uu____24546 with
                               | (lbs5,e22) ->
                                   ((let uu____24566 =
                                       FStar_TypeChecker_Rel.discharge_guard
                                         env1 g_lbs1
                                        in
                                     FStar_All.pipe_right uu____24566
                                       (FStar_TypeChecker_Rel.force_trivial_guard
                                          env1));
                                    (let uu____24567 =
                                       FStar_Syntax_Syntax.mk
                                         (FStar_Syntax_Syntax.Tm_let
                                            ((true, lbs5), e22))
                                         FStar_Pervasives_Native.None
                                         top.FStar_Syntax_Syntax.pos
                                        in
                                     (uu____24567, cres,
                                       FStar_TypeChecker_Env.trivial_guard))))))))
      | uu____24581 -> failwith "Impossible"

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
          let uu____24617 = FStar_Syntax_Subst.open_let_rec lbs e2  in
          (match uu____24617 with
           | (lbs1,e21) ->
               let uu____24636 =
                 FStar_TypeChecker_Env.clear_expected_typ env1  in
               (match uu____24636 with
                | (env0,topt) ->
                    let uu____24655 = build_let_rec_env false env0 lbs1  in
                    (match uu____24655 with
                     | (lbs2,rec_env,g_t) ->
                         let uu____24678 =
                           let uu____24685 = check_let_recs rec_env lbs2  in
                           FStar_All.pipe_right uu____24685
                             (fun uu____24708  ->
                                match uu____24708 with
                                | (lbs3,g) ->
                                    let uu____24727 =
                                      FStar_TypeChecker_Env.conj_guard g_t g
                                       in
                                    (lbs3, uu____24727))
                            in
                         (match uu____24678 with
                          | (lbs3,g_lbs) ->
                              let uu____24742 =
                                FStar_All.pipe_right lbs3
                                  (FStar_Util.fold_map
                                     (fun env2  ->
                                        fun lb  ->
                                          let x =
                                            let uu___3165_24765 =
                                              FStar_Util.left
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___3165_24765.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___3165_24765.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort =
                                                (lb.FStar_Syntax_Syntax.lbtyp)
                                            }  in
                                          let lb1 =
                                            let uu___3168_24767 = lb  in
                                            {
                                              FStar_Syntax_Syntax.lbname =
                                                (FStar_Util.Inl x);
                                              FStar_Syntax_Syntax.lbunivs =
                                                (uu___3168_24767.FStar_Syntax_Syntax.lbunivs);
                                              FStar_Syntax_Syntax.lbtyp =
                                                (uu___3168_24767.FStar_Syntax_Syntax.lbtyp);
                                              FStar_Syntax_Syntax.lbeff =
                                                (uu___3168_24767.FStar_Syntax_Syntax.lbeff);
                                              FStar_Syntax_Syntax.lbdef =
                                                (uu___3168_24767.FStar_Syntax_Syntax.lbdef);
                                              FStar_Syntax_Syntax.lbattrs =
                                                (uu___3168_24767.FStar_Syntax_Syntax.lbattrs);
                                              FStar_Syntax_Syntax.lbpos =
                                                (uu___3168_24767.FStar_Syntax_Syntax.lbpos)
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
                              (match uu____24742 with
                               | (env2,lbs4) ->
                                   let bvs =
                                     FStar_All.pipe_right lbs4
                                       (FStar_List.map
                                          (fun lb  ->
                                             FStar_Util.left
                                               lb.FStar_Syntax_Syntax.lbname))
                                      in
                                   let uu____24794 = tc_term env2 e21  in
                                   (match uu____24794 with
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
                                          let uu____24818 =
                                            let uu____24819 =
                                              FStar_List.map
                                                FStar_Syntax_Syntax.mk_binder
                                                bvs
                                               in
                                            FStar_TypeChecker_Env.close_guard
                                              env2 uu____24819 g2
                                             in
                                          FStar_TypeChecker_Env.conj_guard
                                            g_lbs uu____24818
                                           in
                                        let cres4 =
                                          FStar_TypeChecker_Util.close_wp_lcomp
                                            env2 bvs cres3
                                           in
                                        let tres =
                                          norm env2
                                            cres4.FStar_TypeChecker_Common.res_typ
                                           in
                                        let cres5 =
                                          let uu___3189_24829 = cres4  in
                                          {
                                            FStar_TypeChecker_Common.eff_name
                                              =
                                              (uu___3189_24829.FStar_TypeChecker_Common.eff_name);
                                            FStar_TypeChecker_Common.res_typ
                                              = tres;
                                            FStar_TypeChecker_Common.cflags =
                                              (uu___3189_24829.FStar_TypeChecker_Common.cflags);
                                            FStar_TypeChecker_Common.comp_thunk
                                              =
                                              (uu___3189_24829.FStar_TypeChecker_Common.comp_thunk)
                                          }  in
                                        let guard1 =
                                          let bs =
                                            FStar_All.pipe_right lbs4
                                              (FStar_List.map
                                                 (fun lb  ->
                                                    let uu____24837 =
                                                      FStar_Util.left
                                                        lb.FStar_Syntax_Syntax.lbname
                                                       in
                                                    FStar_Syntax_Syntax.mk_binder
                                                      uu____24837))
                                             in
                                          FStar_TypeChecker_Util.close_guard_implicits
                                            env2 bs guard
                                           in
                                        let uu____24838 =
                                          FStar_Syntax_Subst.close_let_rec
                                            lbs4 e22
                                           in
                                        (match uu____24838 with
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
                                                  uu____24879 ->
                                                  (e, cres5, guard1)
                                              | FStar_Pervasives_Native.None 
                                                  ->
                                                  let uu____24880 =
                                                    check_no_escape
                                                      FStar_Pervasives_Native.None
                                                      env2 bvs tres
                                                     in
                                                  (match uu____24880 with
                                                   | (tres1,g_ex) ->
                                                       let cres6 =
                                                         let uu___3205_24894
                                                           = cres5  in
                                                         {
                                                           FStar_TypeChecker_Common.eff_name
                                                             =
                                                             (uu___3205_24894.FStar_TypeChecker_Common.eff_name);
                                                           FStar_TypeChecker_Common.res_typ
                                                             = tres1;
                                                           FStar_TypeChecker_Common.cflags
                                                             =
                                                             (uu___3205_24894.FStar_TypeChecker_Common.cflags);
                                                           FStar_TypeChecker_Common.comp_thunk
                                                             =
                                                             (uu___3205_24894.FStar_TypeChecker_Common.comp_thunk)
                                                         }  in
                                                       let uu____24895 =
                                                         FStar_TypeChecker_Env.conj_guard
                                                           g_ex guard1
                                                          in
                                                       (e, cres6,
                                                         uu____24895))))))))))
      | uu____24896 -> failwith "Impossible"

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
          let uu____24944 = FStar_Options.ml_ish ()  in
          if uu____24944
          then false
          else
            (let t = FStar_TypeChecker_Normalize.unfold_whnf env lbtyp  in
             let uu____24952 = FStar_Syntax_Util.arrow_formals_comp t  in
             match uu____24952 with
             | (formals,c) ->
                 let uu____24984 = FStar_Syntax_Util.abs_formals lbdef  in
                 (match uu____24984 with
                  | (actuals,uu____24995,uu____24996) ->
                      if
                        ((FStar_List.length formals) < Prims.int_one) ||
                          ((FStar_List.length actuals) < Prims.int_one)
                      then
                        let uu____25017 =
                          let uu____25023 =
                            let uu____25025 =
                              FStar_Syntax_Print.term_to_string lbdef  in
                            let uu____25027 =
                              FStar_Syntax_Print.term_to_string lbtyp  in
                            FStar_Util.format2
                              "Only function literals with arrow types can be defined recursively; got %s : %s"
                              uu____25025 uu____25027
                             in
                          (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                            uu____25023)
                           in
                        FStar_Errors.raise_error uu____25017
                          lbtyp.FStar_Syntax_Syntax.pos
                      else
                        (let actuals1 =
                           let uu____25035 =
                             FStar_TypeChecker_Env.set_expected_typ env lbtyp
                              in
                           FStar_TypeChecker_Util.maybe_add_implicit_binders
                             uu____25035 actuals
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
                                (let uu____25066 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments were found"
                                   uu____25066)
                               in
                            let formals_msg =
                              let n1 = FStar_List.length formals  in
                              if n1 = Prims.int_one
                              then "1 argument"
                              else
                                (let uu____25085 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format1 "%s arguments"
                                   uu____25085)
                               in
                            let msg =
                              let uu____25090 =
                                FStar_Syntax_Print.term_to_string lbtyp  in
                              let uu____25092 =
                                FStar_Syntax_Print.lbname_to_string lbname
                                 in
                              FStar_Util.format4
                                "From its type %s, the definition of `let rec %s` expects a function with %s, but %s"
                                uu____25090 uu____25092 formals_msg
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
        let uu____25104 =
          FStar_List.fold_left
            (fun uu____25137  ->
               fun lb  ->
                 match uu____25137 with
                 | (lbs1,env1,g_acc) ->
                     let uu____25162 =
                       FStar_TypeChecker_Util.extract_let_rec_annotation env1
                         lb
                        in
                     (match uu____25162 with
                      | (univ_vars1,t,check_t) ->
                          let env2 =
                            FStar_TypeChecker_Env.push_univ_vars env1
                              univ_vars1
                             in
                          let e =
                            FStar_Syntax_Util.unascribe
                              lb.FStar_Syntax_Syntax.lbdef
                             in
                          let uu____25185 =
                            if Prims.op_Negation check_t
                            then (g_acc, t)
                            else
                              (let env01 =
                                 FStar_TypeChecker_Env.push_univ_vars env0
                                   univ_vars1
                                  in
                               let uu____25204 =
                                 let uu____25211 =
                                   let uu____25212 =
                                     FStar_Syntax_Util.type_u ()  in
                                   FStar_All.pipe_left
                                     FStar_Pervasives_Native.fst uu____25212
                                    in
                                 tc_check_tot_or_gtot_term
                                   (let uu___3251_25223 = env01  in
                                    {
                                      FStar_TypeChecker_Env.solver =
                                        (uu___3251_25223.FStar_TypeChecker_Env.solver);
                                      FStar_TypeChecker_Env.range =
                                        (uu___3251_25223.FStar_TypeChecker_Env.range);
                                      FStar_TypeChecker_Env.curmodule =
                                        (uu___3251_25223.FStar_TypeChecker_Env.curmodule);
                                      FStar_TypeChecker_Env.gamma =
                                        (uu___3251_25223.FStar_TypeChecker_Env.gamma);
                                      FStar_TypeChecker_Env.gamma_sig =
                                        (uu___3251_25223.FStar_TypeChecker_Env.gamma_sig);
                                      FStar_TypeChecker_Env.gamma_cache =
                                        (uu___3251_25223.FStar_TypeChecker_Env.gamma_cache);
                                      FStar_TypeChecker_Env.modules =
                                        (uu___3251_25223.FStar_TypeChecker_Env.modules);
                                      FStar_TypeChecker_Env.expected_typ =
                                        (uu___3251_25223.FStar_TypeChecker_Env.expected_typ);
                                      FStar_TypeChecker_Env.sigtab =
                                        (uu___3251_25223.FStar_TypeChecker_Env.sigtab);
                                      FStar_TypeChecker_Env.attrtab =
                                        (uu___3251_25223.FStar_TypeChecker_Env.attrtab);
                                      FStar_TypeChecker_Env.is_pattern =
                                        (uu___3251_25223.FStar_TypeChecker_Env.is_pattern);
                                      FStar_TypeChecker_Env.instantiate_imp =
                                        (uu___3251_25223.FStar_TypeChecker_Env.instantiate_imp);
                                      FStar_TypeChecker_Env.effects =
                                        (uu___3251_25223.FStar_TypeChecker_Env.effects);
                                      FStar_TypeChecker_Env.generalize =
                                        (uu___3251_25223.FStar_TypeChecker_Env.generalize);
                                      FStar_TypeChecker_Env.letrecs =
                                        (uu___3251_25223.FStar_TypeChecker_Env.letrecs);
                                      FStar_TypeChecker_Env.top_level =
                                        (uu___3251_25223.FStar_TypeChecker_Env.top_level);
                                      FStar_TypeChecker_Env.check_uvars =
                                        true;
                                      FStar_TypeChecker_Env.use_eq =
                                        (uu___3251_25223.FStar_TypeChecker_Env.use_eq);
                                      FStar_TypeChecker_Env.is_iface =
                                        (uu___3251_25223.FStar_TypeChecker_Env.is_iface);
                                      FStar_TypeChecker_Env.admit =
                                        (uu___3251_25223.FStar_TypeChecker_Env.admit);
                                      FStar_TypeChecker_Env.lax =
                                        (uu___3251_25223.FStar_TypeChecker_Env.lax);
                                      FStar_TypeChecker_Env.lax_universes =
                                        (uu___3251_25223.FStar_TypeChecker_Env.lax_universes);
                                      FStar_TypeChecker_Env.phase1 =
                                        (uu___3251_25223.FStar_TypeChecker_Env.phase1);
                                      FStar_TypeChecker_Env.failhard =
                                        (uu___3251_25223.FStar_TypeChecker_Env.failhard);
                                      FStar_TypeChecker_Env.nosynth =
                                        (uu___3251_25223.FStar_TypeChecker_Env.nosynth);
                                      FStar_TypeChecker_Env.uvar_subtyping =
                                        (uu___3251_25223.FStar_TypeChecker_Env.uvar_subtyping);
                                      FStar_TypeChecker_Env.tc_term =
                                        (uu___3251_25223.FStar_TypeChecker_Env.tc_term);
                                      FStar_TypeChecker_Env.type_of =
                                        (uu___3251_25223.FStar_TypeChecker_Env.type_of);
                                      FStar_TypeChecker_Env.universe_of =
                                        (uu___3251_25223.FStar_TypeChecker_Env.universe_of);
                                      FStar_TypeChecker_Env.check_type_of =
                                        (uu___3251_25223.FStar_TypeChecker_Env.check_type_of);
                                      FStar_TypeChecker_Env.use_bv_sorts =
                                        (uu___3251_25223.FStar_TypeChecker_Env.use_bv_sorts);
                                      FStar_TypeChecker_Env.qtbl_name_and_index
                                        =
                                        (uu___3251_25223.FStar_TypeChecker_Env.qtbl_name_and_index);
                                      FStar_TypeChecker_Env.normalized_eff_names
                                        =
                                        (uu___3251_25223.FStar_TypeChecker_Env.normalized_eff_names);
                                      FStar_TypeChecker_Env.fv_delta_depths =
                                        (uu___3251_25223.FStar_TypeChecker_Env.fv_delta_depths);
                                      FStar_TypeChecker_Env.proof_ns =
                                        (uu___3251_25223.FStar_TypeChecker_Env.proof_ns);
                                      FStar_TypeChecker_Env.synth_hook =
                                        (uu___3251_25223.FStar_TypeChecker_Env.synth_hook);
                                      FStar_TypeChecker_Env.try_solve_implicits_hook
                                        =
                                        (uu___3251_25223.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                      FStar_TypeChecker_Env.splice =
                                        (uu___3251_25223.FStar_TypeChecker_Env.splice);
                                      FStar_TypeChecker_Env.postprocess =
                                        (uu___3251_25223.FStar_TypeChecker_Env.postprocess);
                                      FStar_TypeChecker_Env.is_native_tactic
                                        =
                                        (uu___3251_25223.FStar_TypeChecker_Env.is_native_tactic);
                                      FStar_TypeChecker_Env.identifier_info =
                                        (uu___3251_25223.FStar_TypeChecker_Env.identifier_info);
                                      FStar_TypeChecker_Env.tc_hooks =
                                        (uu___3251_25223.FStar_TypeChecker_Env.tc_hooks);
                                      FStar_TypeChecker_Env.dsenv =
                                        (uu___3251_25223.FStar_TypeChecker_Env.dsenv);
                                      FStar_TypeChecker_Env.nbe =
                                        (uu___3251_25223.FStar_TypeChecker_Env.nbe);
                                      FStar_TypeChecker_Env.strict_args_tab =
                                        (uu___3251_25223.FStar_TypeChecker_Env.strict_args_tab);
                                      FStar_TypeChecker_Env.erasable_types_tab
                                        =
                                        (uu___3251_25223.FStar_TypeChecker_Env.erasable_types_tab)
                                    }) t uu____25211
                                  in
                               match uu____25204 with
                               | (t1,uu____25232,g) ->
                                   let uu____25234 =
                                     let uu____25235 =
                                       let uu____25236 =
                                         FStar_All.pipe_right g
                                           (FStar_TypeChecker_Rel.resolve_implicits
                                              env2)
                                          in
                                       FStar_All.pipe_right uu____25236
                                         (FStar_TypeChecker_Rel.discharge_guard
                                            env2)
                                        in
                                     FStar_TypeChecker_Env.conj_guard g_acc
                                       uu____25235
                                      in
                                   let uu____25237 = norm env01 t1  in
                                   (uu____25234, uu____25237))
                             in
                          (match uu____25185 with
                           | (g,t1) ->
                               let env3 =
                                 let uu____25257 =
                                   termination_check_enabled
                                     lb.FStar_Syntax_Syntax.lbname e t1
                                    in
                                 if uu____25257
                                 then
                                   let uu___3261_25260 = env2  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___3261_25260.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___3261_25260.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___3261_25260.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___3261_25260.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_sig =
                                       (uu___3261_25260.FStar_TypeChecker_Env.gamma_sig);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___3261_25260.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___3261_25260.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___3261_25260.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___3261_25260.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.attrtab =
                                       (uu___3261_25260.FStar_TypeChecker_Env.attrtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___3261_25260.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___3261_25260.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___3261_25260.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___3261_25260.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (((lb.FStar_Syntax_Syntax.lbname), t1,
                                          univ_vars1) ::
                                       (env2.FStar_TypeChecker_Env.letrecs));
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___3261_25260.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___3261_25260.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___3261_25260.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___3261_25260.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___3261_25260.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax =
                                       (uu___3261_25260.FStar_TypeChecker_Env.lax);
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___3261_25260.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.phase1 =
                                       (uu___3261_25260.FStar_TypeChecker_Env.phase1);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___3261_25260.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___3261_25260.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.uvar_subtyping =
                                       (uu___3261_25260.FStar_TypeChecker_Env.uvar_subtyping);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___3261_25260.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___3261_25260.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___3261_25260.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.check_type_of =
                                       (uu___3261_25260.FStar_TypeChecker_Env.check_type_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___3261_25260.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qtbl_name_and_index
                                       =
                                       (uu___3261_25260.FStar_TypeChecker_Env.qtbl_name_and_index);
                                     FStar_TypeChecker_Env.normalized_eff_names
                                       =
                                       (uu___3261_25260.FStar_TypeChecker_Env.normalized_eff_names);
                                     FStar_TypeChecker_Env.fv_delta_depths =
                                       (uu___3261_25260.FStar_TypeChecker_Env.fv_delta_depths);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___3261_25260.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth_hook =
                                       (uu___3261_25260.FStar_TypeChecker_Env.synth_hook);
                                     FStar_TypeChecker_Env.try_solve_implicits_hook
                                       =
                                       (uu___3261_25260.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                     FStar_TypeChecker_Env.splice =
                                       (uu___3261_25260.FStar_TypeChecker_Env.splice);
                                     FStar_TypeChecker_Env.postprocess =
                                       (uu___3261_25260.FStar_TypeChecker_Env.postprocess);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___3261_25260.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___3261_25260.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___3261_25260.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___3261_25260.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.nbe =
                                       (uu___3261_25260.FStar_TypeChecker_Env.nbe);
                                     FStar_TypeChecker_Env.strict_args_tab =
                                       (uu___3261_25260.FStar_TypeChecker_Env.strict_args_tab);
                                     FStar_TypeChecker_Env.erasable_types_tab
                                       =
                                       (uu___3261_25260.FStar_TypeChecker_Env.erasable_types_tab)
                                   }
                                 else
                                   FStar_TypeChecker_Env.push_let_binding
                                     env2 lb.FStar_Syntax_Syntax.lbname
                                     (univ_vars1, t1)
                                  in
                               let lb1 =
                                 let uu___3264_25274 = lb  in
                                 {
                                   FStar_Syntax_Syntax.lbname =
                                     (uu___3264_25274.FStar_Syntax_Syntax.lbname);
                                   FStar_Syntax_Syntax.lbunivs = univ_vars1;
                                   FStar_Syntax_Syntax.lbtyp = t1;
                                   FStar_Syntax_Syntax.lbeff =
                                     (uu___3264_25274.FStar_Syntax_Syntax.lbeff);
                                   FStar_Syntax_Syntax.lbdef = e;
                                   FStar_Syntax_Syntax.lbattrs =
                                     (uu___3264_25274.FStar_Syntax_Syntax.lbattrs);
                                   FStar_Syntax_Syntax.lbpos =
                                     (uu___3264_25274.FStar_Syntax_Syntax.lbpos)
                                 }  in
                               ((lb1 :: lbs1), env3, g))))
            ([], env, FStar_TypeChecker_Env.trivial_guard) lbs
           in
        match uu____25104 with
        | (lbs1,env1,g) -> ((FStar_List.rev lbs1), env1, g)

and (check_let_recs :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      (FStar_Syntax_Syntax.letbinding Prims.list *
        FStar_TypeChecker_Env.guard_t))
  =
  fun env  ->
    fun lbs  ->
      let uu____25300 =
        let uu____25309 =
          FStar_All.pipe_right lbs
            (FStar_List.map
               (fun lb  ->
                  let uu____25335 =
                    FStar_Syntax_Util.abs_formals
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  match uu____25335 with
                  | (bs,t,lcomp) ->
                      (match bs with
                       | [] ->
                           let uu____25365 =
                             FStar_Syntax_Syntax.range_of_lbname
                               lb.FStar_Syntax_Syntax.lbname
                              in
                           FStar_Errors.raise_error
                             (FStar_Errors.Fatal_RecursiveFunctionLiteral,
                               "Only function literals may be defined recursively")
                             uu____25365
                       | uu____25372 ->
                           let lb1 =
                             let uu___3281_25375 = lb  in
                             let uu____25376 =
                               FStar_Syntax_Util.abs bs t lcomp  in
                             {
                               FStar_Syntax_Syntax.lbname =
                                 (uu___3281_25375.FStar_Syntax_Syntax.lbname);
                               FStar_Syntax_Syntax.lbunivs =
                                 (uu___3281_25375.FStar_Syntax_Syntax.lbunivs);
                               FStar_Syntax_Syntax.lbtyp =
                                 (uu___3281_25375.FStar_Syntax_Syntax.lbtyp);
                               FStar_Syntax_Syntax.lbeff =
                                 (uu___3281_25375.FStar_Syntax_Syntax.lbeff);
                               FStar_Syntax_Syntax.lbdef = uu____25376;
                               FStar_Syntax_Syntax.lbattrs =
                                 (uu___3281_25375.FStar_Syntax_Syntax.lbattrs);
                               FStar_Syntax_Syntax.lbpos =
                                 (uu___3281_25375.FStar_Syntax_Syntax.lbpos)
                             }  in
                           let uu____25379 =
                             let uu____25386 =
                               FStar_TypeChecker_Env.set_expected_typ env
                                 lb1.FStar_Syntax_Syntax.lbtyp
                                in
                             tc_tot_or_gtot_term uu____25386
                               lb1.FStar_Syntax_Syntax.lbdef
                              in
                           (match uu____25379 with
                            | (e,c,g) ->
                                ((let uu____25395 =
                                    let uu____25397 =
                                      FStar_TypeChecker_Common.is_total_lcomp
                                        c
                                       in
                                    Prims.op_Negation uu____25397  in
                                  if uu____25395
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
        FStar_All.pipe_right uu____25309 FStar_List.unzip  in
      match uu____25300 with
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
        let uu____25453 = FStar_TypeChecker_Env.clear_expected_typ env  in
        match uu____25453 with
        | (env1,uu____25472) ->
            let e1 = lb.FStar_Syntax_Syntax.lbdef  in
            let uu____25480 = check_lbtyp top_level env lb  in
            (match uu____25480 with
             | (topt,wf_annot,univ_vars1,univ_opening,env11) ->
                 (if (Prims.op_Negation top_level) && (univ_vars1 <> [])
                  then
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_UniversePolymorphicInnerLetBound,
                        "Inner let-bound definitions cannot be universe polymorphic")
                      e1.FStar_Syntax_Syntax.pos
                  else ();
                  (let e11 = FStar_Syntax_Subst.subst univ_opening e1  in
                   let uu____25529 =
                     tc_maybe_toplevel_term
                       (let uu___3312_25538 = env11  in
                        {
                          FStar_TypeChecker_Env.solver =
                            (uu___3312_25538.FStar_TypeChecker_Env.solver);
                          FStar_TypeChecker_Env.range =
                            (uu___3312_25538.FStar_TypeChecker_Env.range);
                          FStar_TypeChecker_Env.curmodule =
                            (uu___3312_25538.FStar_TypeChecker_Env.curmodule);
                          FStar_TypeChecker_Env.gamma =
                            (uu___3312_25538.FStar_TypeChecker_Env.gamma);
                          FStar_TypeChecker_Env.gamma_sig =
                            (uu___3312_25538.FStar_TypeChecker_Env.gamma_sig);
                          FStar_TypeChecker_Env.gamma_cache =
                            (uu___3312_25538.FStar_TypeChecker_Env.gamma_cache);
                          FStar_TypeChecker_Env.modules =
                            (uu___3312_25538.FStar_TypeChecker_Env.modules);
                          FStar_TypeChecker_Env.expected_typ =
                            (uu___3312_25538.FStar_TypeChecker_Env.expected_typ);
                          FStar_TypeChecker_Env.sigtab =
                            (uu___3312_25538.FStar_TypeChecker_Env.sigtab);
                          FStar_TypeChecker_Env.attrtab =
                            (uu___3312_25538.FStar_TypeChecker_Env.attrtab);
                          FStar_TypeChecker_Env.is_pattern =
                            (uu___3312_25538.FStar_TypeChecker_Env.is_pattern);
                          FStar_TypeChecker_Env.instantiate_imp =
                            (uu___3312_25538.FStar_TypeChecker_Env.instantiate_imp);
                          FStar_TypeChecker_Env.effects =
                            (uu___3312_25538.FStar_TypeChecker_Env.effects);
                          FStar_TypeChecker_Env.generalize =
                            (uu___3312_25538.FStar_TypeChecker_Env.generalize);
                          FStar_TypeChecker_Env.letrecs =
                            (uu___3312_25538.FStar_TypeChecker_Env.letrecs);
                          FStar_TypeChecker_Env.top_level = top_level;
                          FStar_TypeChecker_Env.check_uvars =
                            (uu___3312_25538.FStar_TypeChecker_Env.check_uvars);
                          FStar_TypeChecker_Env.use_eq =
                            (uu___3312_25538.FStar_TypeChecker_Env.use_eq);
                          FStar_TypeChecker_Env.is_iface =
                            (uu___3312_25538.FStar_TypeChecker_Env.is_iface);
                          FStar_TypeChecker_Env.admit =
                            (uu___3312_25538.FStar_TypeChecker_Env.admit);
                          FStar_TypeChecker_Env.lax =
                            (uu___3312_25538.FStar_TypeChecker_Env.lax);
                          FStar_TypeChecker_Env.lax_universes =
                            (uu___3312_25538.FStar_TypeChecker_Env.lax_universes);
                          FStar_TypeChecker_Env.phase1 =
                            (uu___3312_25538.FStar_TypeChecker_Env.phase1);
                          FStar_TypeChecker_Env.failhard =
                            (uu___3312_25538.FStar_TypeChecker_Env.failhard);
                          FStar_TypeChecker_Env.nosynth =
                            (uu___3312_25538.FStar_TypeChecker_Env.nosynth);
                          FStar_TypeChecker_Env.uvar_subtyping =
                            (uu___3312_25538.FStar_TypeChecker_Env.uvar_subtyping);
                          FStar_TypeChecker_Env.tc_term =
                            (uu___3312_25538.FStar_TypeChecker_Env.tc_term);
                          FStar_TypeChecker_Env.type_of =
                            (uu___3312_25538.FStar_TypeChecker_Env.type_of);
                          FStar_TypeChecker_Env.universe_of =
                            (uu___3312_25538.FStar_TypeChecker_Env.universe_of);
                          FStar_TypeChecker_Env.check_type_of =
                            (uu___3312_25538.FStar_TypeChecker_Env.check_type_of);
                          FStar_TypeChecker_Env.use_bv_sorts =
                            (uu___3312_25538.FStar_TypeChecker_Env.use_bv_sorts);
                          FStar_TypeChecker_Env.qtbl_name_and_index =
                            (uu___3312_25538.FStar_TypeChecker_Env.qtbl_name_and_index);
                          FStar_TypeChecker_Env.normalized_eff_names =
                            (uu___3312_25538.FStar_TypeChecker_Env.normalized_eff_names);
                          FStar_TypeChecker_Env.fv_delta_depths =
                            (uu___3312_25538.FStar_TypeChecker_Env.fv_delta_depths);
                          FStar_TypeChecker_Env.proof_ns =
                            (uu___3312_25538.FStar_TypeChecker_Env.proof_ns);
                          FStar_TypeChecker_Env.synth_hook =
                            (uu___3312_25538.FStar_TypeChecker_Env.synth_hook);
                          FStar_TypeChecker_Env.try_solve_implicits_hook =
                            (uu___3312_25538.FStar_TypeChecker_Env.try_solve_implicits_hook);
                          FStar_TypeChecker_Env.splice =
                            (uu___3312_25538.FStar_TypeChecker_Env.splice);
                          FStar_TypeChecker_Env.postprocess =
                            (uu___3312_25538.FStar_TypeChecker_Env.postprocess);
                          FStar_TypeChecker_Env.is_native_tactic =
                            (uu___3312_25538.FStar_TypeChecker_Env.is_native_tactic);
                          FStar_TypeChecker_Env.identifier_info =
                            (uu___3312_25538.FStar_TypeChecker_Env.identifier_info);
                          FStar_TypeChecker_Env.tc_hooks =
                            (uu___3312_25538.FStar_TypeChecker_Env.tc_hooks);
                          FStar_TypeChecker_Env.dsenv =
                            (uu___3312_25538.FStar_TypeChecker_Env.dsenv);
                          FStar_TypeChecker_Env.nbe =
                            (uu___3312_25538.FStar_TypeChecker_Env.nbe);
                          FStar_TypeChecker_Env.strict_args_tab =
                            (uu___3312_25538.FStar_TypeChecker_Env.strict_args_tab);
                          FStar_TypeChecker_Env.erasable_types_tab =
                            (uu___3312_25538.FStar_TypeChecker_Env.erasable_types_tab)
                        }) e11
                      in
                   match uu____25529 with
                   | (e12,c1,g1) ->
                       let uu____25553 =
                         let uu____25558 =
                           FStar_TypeChecker_Env.set_range env11
                             e12.FStar_Syntax_Syntax.pos
                            in
                         FStar_TypeChecker_Util.strengthen_precondition
                           (FStar_Pervasives_Native.Some
                              (fun uu____25564  ->
                                 FStar_Util.return_all
                                   FStar_TypeChecker_Err.ill_kinded_type))
                           uu____25558 e12 c1 wf_annot
                          in
                       (match uu____25553 with
                        | (c11,guard_f) ->
                            let g11 =
                              FStar_TypeChecker_Env.conj_guard g1 guard_f  in
                            ((let uu____25581 =
                                FStar_TypeChecker_Env.debug env
                                  FStar_Options.Extreme
                                 in
                              if uu____25581
                              then
                                let uu____25584 =
                                  FStar_Syntax_Print.lbname_to_string
                                    lb.FStar_Syntax_Syntax.lbname
                                   in
                                let uu____25586 =
                                  FStar_TypeChecker_Common.lcomp_to_string
                                    c11
                                   in
                                let uu____25588 =
                                  FStar_TypeChecker_Rel.guard_to_string env
                                    g11
                                   in
                                FStar_Util.print3
                                  "checked let-bound def %s : %s guard is %s\n"
                                  uu____25584 uu____25586 uu____25588
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
            let uu____25627 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____25627 with
             | (univ_opening,univ_vars1) ->
                 let uu____25660 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 (FStar_Pervasives_Native.None,
                   FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                   univ_opening, uu____25660))
        | uu____25665 ->
            let uu____25666 =
              FStar_Syntax_Subst.univ_var_opening
                lb.FStar_Syntax_Syntax.lbunivs
               in
            (match uu____25666 with
             | (univ_opening,univ_vars1) ->
                 let t1 = FStar_Syntax_Subst.subst univ_opening t  in
                 let env1 =
                   FStar_TypeChecker_Env.push_univ_vars env univ_vars1  in
                 if
                   top_level &&
                     (Prims.op_Negation env.FStar_TypeChecker_Env.generalize)
                 then
                   let uu____25716 =
                     FStar_TypeChecker_Env.set_expected_typ env1 t1  in
                   ((FStar_Pervasives_Native.Some t1),
                     FStar_TypeChecker_Env.trivial_guard, univ_vars1,
                     univ_opening, uu____25716)
                 else
                   (let uu____25723 = FStar_Syntax_Util.type_u ()  in
                    match uu____25723 with
                    | (k,uu____25743) ->
                        let uu____25744 = tc_check_tot_or_gtot_term env1 t1 k
                           in
                        (match uu____25744 with
                         | (t2,uu____25766,g) ->
                             ((let uu____25769 =
                                 FStar_TypeChecker_Env.debug env
                                   FStar_Options.Medium
                                  in
                               if uu____25769
                               then
                                 let uu____25772 =
                                   let uu____25774 =
                                     FStar_Syntax_Util.range_of_lbname
                                       lb.FStar_Syntax_Syntax.lbname
                                      in
                                   FStar_Range.string_of_range uu____25774
                                    in
                                 let uu____25775 =
                                   FStar_Syntax_Print.term_to_string t2  in
                                 FStar_Util.print2
                                   "(%s) Checked type annotation %s\n"
                                   uu____25772 uu____25775
                               else ());
                              (let t3 = norm env1 t2  in
                               let uu____25781 =
                                 FStar_TypeChecker_Env.set_expected_typ env1
                                   t3
                                  in
                               ((FStar_Pervasives_Native.Some t3), g,
                                 univ_vars1, univ_opening, uu____25781))))))

and (tc_binder :
  FStar_TypeChecker_Env.env ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Env.guard_t * FStar_Syntax_Syntax.universe))
  =
  fun env  ->
    fun uu____25787  ->
      match uu____25787 with
      | (x,imp) ->
          let uu____25814 = FStar_Syntax_Util.type_u ()  in
          (match uu____25814 with
           | (tu,u) ->
               ((let uu____25836 =
                   FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
                 if uu____25836
                 then
                   let uu____25839 = FStar_Syntax_Print.bv_to_string x  in
                   let uu____25841 =
                     FStar_Syntax_Print.term_to_string
                       x.FStar_Syntax_Syntax.sort
                      in
                   let uu____25843 = FStar_Syntax_Print.term_to_string tu  in
                   FStar_Util.print3 "Checking binder %s:%s at type %s\n"
                     uu____25839 uu____25841 uu____25843
                 else ());
                (let uu____25848 =
                   tc_check_tot_or_gtot_term env x.FStar_Syntax_Syntax.sort
                     tu
                    in
                 match uu____25848 with
                 | (t,uu____25870,g) ->
                     let uu____25872 =
                       match imp with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Meta tau) ->
                           let uu____25888 = tc_tactic env tau  in
                           (match uu____25888 with
                            | (tau1,uu____25902,g1) ->
                                ((FStar_Pervasives_Native.Some
                                    (FStar_Syntax_Syntax.Meta tau1)), g1))
                       | uu____25906 ->
                           (imp, FStar_TypeChecker_Env.trivial_guard)
                        in
                     (match uu____25872 with
                      | (imp1,g') ->
                          let x1 =
                            ((let uu___3374_25941 = x  in
                              {
                                FStar_Syntax_Syntax.ppname =
                                  (uu___3374_25941.FStar_Syntax_Syntax.ppname);
                                FStar_Syntax_Syntax.index =
                                  (uu___3374_25941.FStar_Syntax_Syntax.index);
                                FStar_Syntax_Syntax.sort = t
                              }), imp1)
                             in
                          ((let uu____25943 =
                              FStar_TypeChecker_Env.debug env
                                FStar_Options.High
                               in
                            if uu____25943
                            then
                              let uu____25946 =
                                FStar_Syntax_Print.bv_to_string
                                  (FStar_Pervasives_Native.fst x1)
                                 in
                              let uu____25950 =
                                FStar_Syntax_Print.term_to_string t  in
                              FStar_Util.print2
                                "Pushing binder %s at type %s\n" uu____25946
                                uu____25950
                            else ());
                           (let uu____25955 = push_binding env x1  in
                            (x1, uu____25955, g, u)))))))

and (tc_binders :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_TypeChecker_Common.guard_t * FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun bs  ->
      (let uu____25967 =
         FStar_TypeChecker_Env.debug env FStar_Options.Extreme  in
       if uu____25967
       then
         let uu____25970 = FStar_Syntax_Print.binders_to_string ", " bs  in
         FStar_Util.print1 "Checking binders %s\n" uu____25970
       else ());
      (let rec aux env1 bs1 =
         match bs1 with
         | [] -> ([], env1, FStar_TypeChecker_Env.trivial_guard, [])
         | b::bs2 ->
             let uu____26083 = tc_binder env1 b  in
             (match uu____26083 with
              | (b1,env',g,u) ->
                  let uu____26132 = aux env' bs2  in
                  (match uu____26132 with
                   | (bs3,env'1,g',us) ->
                       let uu____26193 =
                         let uu____26194 =
                           FStar_TypeChecker_Env.close_guard_univs [u] 
                             [b1] g'
                            in
                         FStar_TypeChecker_Env.conj_guard g uu____26194  in
                       ((b1 :: bs3), env'1, uu____26193, (u :: us))))
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
          (fun uu____26302  ->
             fun uu____26303  ->
               match (uu____26302, uu____26303) with
               | ((t,imp),(args1,g)) ->
                   (FStar_All.pipe_right t (check_no_smt_theory_symbols en1);
                    (let uu____26395 = tc_term en1 t  in
                     match uu____26395 with
                     | (t1,uu____26415,g') ->
                         let uu____26417 =
                           FStar_TypeChecker_Env.conj_guard g g'  in
                         (((t1, imp) :: args1), uu____26417)))) args
          ([], FStar_TypeChecker_Env.trivial_guard)
         in
      FStar_List.fold_right
        (fun p  ->
           fun uu____26471  ->
             match uu____26471 with
             | (pats1,g) ->
                 let uu____26498 = tc_args en p  in
                 (match uu____26498 with
                  | (args,g') ->
                      let uu____26511 = FStar_TypeChecker_Env.conj_guard g g'
                         in
                      ((args :: pats1), uu____26511))) pats
        ([], FStar_TypeChecker_Env.trivial_guard)

and (tc_tot_or_gtot_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t))
  =
  fun env  ->
    fun e  ->
      let uu____26524 = tc_maybe_toplevel_term env e  in
      match uu____26524 with
      | (e1,c,g) ->
          let uu____26540 = FStar_TypeChecker_Common.is_tot_or_gtot_lcomp c
             in
          if uu____26540
          then (e1, c, g)
          else
            (let g1 = FStar_TypeChecker_Rel.solve_deferred_constraints env g
                in
             let uu____26552 = FStar_TypeChecker_Common.lcomp_comp c  in
             match uu____26552 with
             | (c1,g_c) ->
                 let c2 = norm_c env c1  in
                 let uu____26566 =
                   let uu____26572 =
                     FStar_TypeChecker_Util.is_pure_effect env
                       (FStar_Syntax_Util.comp_effect_name c2)
                      in
                   if uu____26572
                   then
                     let uu____26580 =
                       FStar_Syntax_Syntax.mk_Total
                         (FStar_Syntax_Util.comp_result c2)
                        in
                     (uu____26580, false)
                   else
                     (let uu____26585 =
                        FStar_Syntax_Syntax.mk_GTotal
                          (FStar_Syntax_Util.comp_result c2)
                         in
                      (uu____26585, true))
                    in
                 (match uu____26566 with
                  | (target_comp,allow_ghost) ->
                      let uu____26598 =
                        FStar_TypeChecker_Rel.sub_comp env c2 target_comp  in
                      (match uu____26598 with
                       | FStar_Pervasives_Native.Some g' ->
                           let uu____26608 =
                             FStar_TypeChecker_Common.lcomp_of_comp
                               target_comp
                              in
                           let uu____26609 =
                             let uu____26610 =
                               FStar_TypeChecker_Env.conj_guard g_c g'  in
                             FStar_TypeChecker_Env.conj_guard g1 uu____26610
                              in
                           (e1, uu____26608, uu____26609)
                       | uu____26611 ->
                           if allow_ghost
                           then
                             let uu____26621 =
                               FStar_TypeChecker_Err.expected_ghost_expression
                                 e1 c2
                                in
                             FStar_Errors.raise_error uu____26621
                               e1.FStar_Syntax_Syntax.pos
                           else
                             (let uu____26635 =
                                FStar_TypeChecker_Err.expected_pure_expression
                                  e1 c2
                                 in
                              FStar_Errors.raise_error uu____26635
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
      let uu____26659 = tc_tot_or_gtot_term env t  in
      match uu____26659 with
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
      (let uu____26692 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "RelCheck")
          in
       if uu____26692
       then
         let uu____26697 = FStar_Syntax_Print.term_to_string e  in
         FStar_Util.print1 "Checking term %s\n" uu____26697
       else ());
      (let env1 =
         let uu___3458_26703 = env  in
         {
           FStar_TypeChecker_Env.solver =
             (uu___3458_26703.FStar_TypeChecker_Env.solver);
           FStar_TypeChecker_Env.range =
             (uu___3458_26703.FStar_TypeChecker_Env.range);
           FStar_TypeChecker_Env.curmodule =
             (uu___3458_26703.FStar_TypeChecker_Env.curmodule);
           FStar_TypeChecker_Env.gamma =
             (uu___3458_26703.FStar_TypeChecker_Env.gamma);
           FStar_TypeChecker_Env.gamma_sig =
             (uu___3458_26703.FStar_TypeChecker_Env.gamma_sig);
           FStar_TypeChecker_Env.gamma_cache =
             (uu___3458_26703.FStar_TypeChecker_Env.gamma_cache);
           FStar_TypeChecker_Env.modules =
             (uu___3458_26703.FStar_TypeChecker_Env.modules);
           FStar_TypeChecker_Env.expected_typ =
             (uu___3458_26703.FStar_TypeChecker_Env.expected_typ);
           FStar_TypeChecker_Env.sigtab =
             (uu___3458_26703.FStar_TypeChecker_Env.sigtab);
           FStar_TypeChecker_Env.attrtab =
             (uu___3458_26703.FStar_TypeChecker_Env.attrtab);
           FStar_TypeChecker_Env.is_pattern =
             (uu___3458_26703.FStar_TypeChecker_Env.is_pattern);
           FStar_TypeChecker_Env.instantiate_imp =
             (uu___3458_26703.FStar_TypeChecker_Env.instantiate_imp);
           FStar_TypeChecker_Env.effects =
             (uu___3458_26703.FStar_TypeChecker_Env.effects);
           FStar_TypeChecker_Env.generalize =
             (uu___3458_26703.FStar_TypeChecker_Env.generalize);
           FStar_TypeChecker_Env.letrecs = [];
           FStar_TypeChecker_Env.top_level = false;
           FStar_TypeChecker_Env.check_uvars =
             (uu___3458_26703.FStar_TypeChecker_Env.check_uvars);
           FStar_TypeChecker_Env.use_eq =
             (uu___3458_26703.FStar_TypeChecker_Env.use_eq);
           FStar_TypeChecker_Env.is_iface =
             (uu___3458_26703.FStar_TypeChecker_Env.is_iface);
           FStar_TypeChecker_Env.admit =
             (uu___3458_26703.FStar_TypeChecker_Env.admit);
           FStar_TypeChecker_Env.lax =
             (uu___3458_26703.FStar_TypeChecker_Env.lax);
           FStar_TypeChecker_Env.lax_universes =
             (uu___3458_26703.FStar_TypeChecker_Env.lax_universes);
           FStar_TypeChecker_Env.phase1 =
             (uu___3458_26703.FStar_TypeChecker_Env.phase1);
           FStar_TypeChecker_Env.failhard =
             (uu___3458_26703.FStar_TypeChecker_Env.failhard);
           FStar_TypeChecker_Env.nosynth =
             (uu___3458_26703.FStar_TypeChecker_Env.nosynth);
           FStar_TypeChecker_Env.uvar_subtyping =
             (uu___3458_26703.FStar_TypeChecker_Env.uvar_subtyping);
           FStar_TypeChecker_Env.tc_term =
             (uu___3458_26703.FStar_TypeChecker_Env.tc_term);
           FStar_TypeChecker_Env.type_of =
             (uu___3458_26703.FStar_TypeChecker_Env.type_of);
           FStar_TypeChecker_Env.universe_of =
             (uu___3458_26703.FStar_TypeChecker_Env.universe_of);
           FStar_TypeChecker_Env.check_type_of =
             (uu___3458_26703.FStar_TypeChecker_Env.check_type_of);
           FStar_TypeChecker_Env.use_bv_sorts =
             (uu___3458_26703.FStar_TypeChecker_Env.use_bv_sorts);
           FStar_TypeChecker_Env.qtbl_name_and_index =
             (uu___3458_26703.FStar_TypeChecker_Env.qtbl_name_and_index);
           FStar_TypeChecker_Env.normalized_eff_names =
             (uu___3458_26703.FStar_TypeChecker_Env.normalized_eff_names);
           FStar_TypeChecker_Env.fv_delta_depths =
             (uu___3458_26703.FStar_TypeChecker_Env.fv_delta_depths);
           FStar_TypeChecker_Env.proof_ns =
             (uu___3458_26703.FStar_TypeChecker_Env.proof_ns);
           FStar_TypeChecker_Env.synth_hook =
             (uu___3458_26703.FStar_TypeChecker_Env.synth_hook);
           FStar_TypeChecker_Env.try_solve_implicits_hook =
             (uu___3458_26703.FStar_TypeChecker_Env.try_solve_implicits_hook);
           FStar_TypeChecker_Env.splice =
             (uu___3458_26703.FStar_TypeChecker_Env.splice);
           FStar_TypeChecker_Env.postprocess =
             (uu___3458_26703.FStar_TypeChecker_Env.postprocess);
           FStar_TypeChecker_Env.is_native_tactic =
             (uu___3458_26703.FStar_TypeChecker_Env.is_native_tactic);
           FStar_TypeChecker_Env.identifier_info =
             (uu___3458_26703.FStar_TypeChecker_Env.identifier_info);
           FStar_TypeChecker_Env.tc_hooks =
             (uu___3458_26703.FStar_TypeChecker_Env.tc_hooks);
           FStar_TypeChecker_Env.dsenv =
             (uu___3458_26703.FStar_TypeChecker_Env.dsenv);
           FStar_TypeChecker_Env.nbe =
             (uu___3458_26703.FStar_TypeChecker_Env.nbe);
           FStar_TypeChecker_Env.strict_args_tab =
             (uu___3458_26703.FStar_TypeChecker_Env.strict_args_tab);
           FStar_TypeChecker_Env.erasable_types_tab =
             (uu___3458_26703.FStar_TypeChecker_Env.erasable_types_tab)
         }  in
       let uu____26711 =
         try
           (fun uu___3462_26725  ->
              match () with | () -> tc_tot_or_gtot_term env1 e) ()
         with
         | FStar_Errors.Error (e1,msg,uu____26746) ->
             let uu____26749 = FStar_TypeChecker_Env.get_range env1  in
             FStar_Errors.raise_error (e1, msg) uu____26749
          in
       match uu____26711 with
       | (t,c,g) ->
           let c1 = FStar_TypeChecker_Normalize.ghost_to_pure_lcomp env1 c
              in
           let uu____26767 = FStar_TypeChecker_Common.is_total_lcomp c1  in
           if uu____26767
           then (t, (c1.FStar_TypeChecker_Common.res_typ), g)
           else
             (let uu____26778 =
                let uu____26784 =
                  let uu____26786 = FStar_Syntax_Print.term_to_string e  in
                  FStar_Util.format1
                    "Implicit argument: Expected a total term; got a ghost term: %s"
                    uu____26786
                   in
                (FStar_Errors.Fatal_UnexpectedImplictArgument, uu____26784)
                 in
              let uu____26790 = FStar_TypeChecker_Env.get_range env1  in
              FStar_Errors.raise_error uu____26778 uu____26790))
  
let level_of_type_fail :
  'Auu____26806 .
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> Prims.string -> 'Auu____26806
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let uu____26824 =
          let uu____26830 =
            let uu____26832 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format2 "Expected a term of type 'Type'; got %s : %s"
              uu____26832 t
             in
          (FStar_Errors.Fatal_UnexpectedTermType, uu____26830)  in
        let uu____26836 = FStar_TypeChecker_Env.get_range env  in
        FStar_Errors.raise_error uu____26824 uu____26836
  
let (level_of_type :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      fun t  ->
        let rec aux retry t1 =
          let uu____26870 =
            let uu____26871 = FStar_Syntax_Util.unrefine t1  in
            uu____26871.FStar_Syntax_Syntax.n  in
          match uu____26870 with
          | FStar_Syntax_Syntax.Tm_type u -> u
          | uu____26875 ->
              if retry
              then
                let t2 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.UnfoldUntil
                       FStar_Syntax_Syntax.delta_constant] env t1
                   in
                aux false t2
              else
                (let uu____26881 = FStar_Syntax_Util.type_u ()  in
                 match uu____26881 with
                 | (t_u,u) ->
                     let env1 =
                       let uu___3494_26889 = env  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3494_26889.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3494_26889.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3494_26889.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3494_26889.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3494_26889.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3494_26889.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3494_26889.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3494_26889.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3494_26889.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3494_26889.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3494_26889.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3494_26889.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3494_26889.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3494_26889.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3494_26889.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (uu___3494_26889.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3494_26889.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3494_26889.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3494_26889.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3494_26889.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3494_26889.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3494_26889.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3494_26889.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3494_26889.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3494_26889.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3494_26889.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3494_26889.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3494_26889.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3494_26889.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts =
                           (uu___3494_26889.FStar_TypeChecker_Env.use_bv_sorts);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3494_26889.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3494_26889.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3494_26889.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3494_26889.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3494_26889.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3494_26889.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3494_26889.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3494_26889.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3494_26889.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3494_26889.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3494_26889.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3494_26889.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3494_26889.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3494_26889.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3494_26889.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     let g = FStar_TypeChecker_Rel.teq env1 t1 t_u  in
                     ((match g.FStar_TypeChecker_Common.guard_f with
                       | FStar_TypeChecker_Common.NonTrivial f ->
                           let uu____26894 =
                             FStar_Syntax_Print.term_to_string t1  in
                           level_of_type_fail env1 e uu____26894
                       | uu____26896 ->
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
      let uu____26913 =
        let uu____26914 = FStar_Syntax_Subst.compress e  in
        uu____26914.FStar_Syntax_Syntax.n  in
      match uu____26913 with
      | FStar_Syntax_Syntax.Tm_bvar uu____26917 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_unknown  -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_delayed uu____26920 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_let uu____26944 ->
          let e1 = FStar_TypeChecker_Normalize.normalize [] env e  in
          universe_of_aux env e1
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____26961) ->
          level_of_type_fail env e "arrow type"
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
      | FStar_Syntax_Syntax.Tm_meta (t,uu____27006) -> universe_of_aux env t
      | FStar_Syntax_Syntax.Tm_name n1 -> n1.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____27013 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27013 with | ((uu____27022,t),uu____27024) -> t)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____27030 = FStar_Syntax_Util.unfold_lazy i  in
          universe_of_aux env uu____27030
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27033,(FStar_Util.Inl t,uu____27035),uu____27036) -> t
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____27083,(FStar_Util.Inr c,uu____27085),uu____27086) ->
          FStar_Syntax_Util.comp_result c
      | FStar_Syntax_Syntax.Tm_type u ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_succ u))
            FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
      | FStar_Syntax_Syntax.Tm_quoted uu____27134 -> FStar_Syntax_Util.ktype0
      | FStar_Syntax_Syntax.Tm_constant sc ->
          tc_constant env e.FStar_Syntax_Syntax.pos sc
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____27143;
             FStar_Syntax_Syntax.vars = uu____27144;_},us)
          ->
          let uu____27150 =
            FStar_TypeChecker_Env.lookup_lid env
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____27150 with
           | ((us',t),uu____27161) ->
               (if (FStar_List.length us) <> (FStar_List.length us')
                then
                  (let uu____27168 = FStar_TypeChecker_Env.get_range env  in
                   FStar_Errors.raise_error
                     (FStar_Errors.Fatal_UnexpectedNumberOfUniverse,
                       "Unexpected number of universe instantiations")
                     uu____27168)
                else
                  FStar_List.iter2
                    (fun u'  ->
                       fun u  ->
                         match u' with
                         | FStar_Syntax_Syntax.U_unif u'' ->
                             FStar_Syntax_Unionfind.univ_change u'' u
                         | uu____27187 -> failwith "Impossible") us' us;
                t))
      | FStar_Syntax_Syntax.Tm_uinst uu____27189 ->
          failwith "Impossible: Tm_uinst's head must be an fvar"
      | FStar_Syntax_Syntax.Tm_refine (x,uu____27198) ->
          universe_of_aux env x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____27225 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____27225 with
           | (bs1,c1) ->
               let us =
                 FStar_List.map
                   (fun uu____27245  ->
                      match uu____27245 with
                      | (b,uu____27253) ->
                          let uu____27258 =
                            universe_of_aux env b.FStar_Syntax_Syntax.sort
                             in
                          level_of_type env b.FStar_Syntax_Syntax.sort
                            uu____27258) bs1
                  in
               let u_res =
                 let res = FStar_Syntax_Util.comp_result c1  in
                 let uu____27263 = universe_of_aux env res  in
                 level_of_type env res uu____27263  in
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
            | FStar_Syntax_Syntax.Tm_bvar uu____27374 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_delayed uu____27390 ->
                failwith "Impossible"
            | FStar_Syntax_Syntax.Tm_fvar uu____27428 ->
                let uu____27429 = universe_of_aux env hd3  in
                (uu____27429, args1)
            | FStar_Syntax_Syntax.Tm_name uu____27440 ->
                let uu____27441 = universe_of_aux env hd3  in
                (uu____27441, args1)
            | FStar_Syntax_Syntax.Tm_uvar uu____27452 ->
                let uu____27465 = universe_of_aux env hd3  in
                (uu____27465, args1)
            | FStar_Syntax_Syntax.Tm_uinst uu____27476 ->
                let uu____27483 = universe_of_aux env hd3  in
                (uu____27483, args1)
            | FStar_Syntax_Syntax.Tm_ascribed uu____27494 ->
                let uu____27521 = universe_of_aux env hd3  in
                (uu____27521, args1)
            | FStar_Syntax_Syntax.Tm_refine uu____27532 ->
                let uu____27539 = universe_of_aux env hd3  in
                (uu____27539, args1)
            | FStar_Syntax_Syntax.Tm_constant uu____27550 ->
                let uu____27551 = universe_of_aux env hd3  in
                (uu____27551, args1)
            | FStar_Syntax_Syntax.Tm_arrow uu____27562 ->
                let uu____27577 = universe_of_aux env hd3  in
                (uu____27577, args1)
            | FStar_Syntax_Syntax.Tm_meta uu____27588 ->
                let uu____27595 = universe_of_aux env hd3  in
                (uu____27595, args1)
            | FStar_Syntax_Syntax.Tm_type uu____27606 ->
                let uu____27607 = universe_of_aux env hd3  in
                (uu____27607, args1)
            | FStar_Syntax_Syntax.Tm_match (uu____27618,hd4::uu____27620) ->
                let uu____27685 = FStar_Syntax_Subst.open_branch hd4  in
                (match uu____27685 with
                 | (uu____27700,uu____27701,hd5) ->
                     let uu____27719 = FStar_Syntax_Util.head_and_args hd5
                        in
                     (match uu____27719 with
                      | (hd6,args2) -> type_of_head retry hd6 args2))
            | uu____27776 when retry ->
                let e1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Env.Beta;
                    FStar_TypeChecker_Env.DoNotUnfoldPureLets] env e
                   in
                let uu____27778 = FStar_Syntax_Util.head_and_args e1  in
                (match uu____27778 with
                 | (hd4,args2) -> type_of_head false hd4 args2)
            | uu____27836 ->
                let uu____27837 =
                  FStar_TypeChecker_Env.clear_expected_typ env  in
                (match uu____27837 with
                 | (env1,uu____27859) ->
                     let env2 =
                       let uu___3655_27865 = env1  in
                       {
                         FStar_TypeChecker_Env.solver =
                           (uu___3655_27865.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (uu___3655_27865.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (uu___3655_27865.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (uu___3655_27865.FStar_TypeChecker_Env.gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (uu___3655_27865.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (uu___3655_27865.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (uu___3655_27865.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (uu___3655_27865.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (uu___3655_27865.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (uu___3655_27865.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.is_pattern =
                           (uu___3655_27865.FStar_TypeChecker_Env.is_pattern);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (uu___3655_27865.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (uu___3655_27865.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (uu___3655_27865.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (uu___3655_27865.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level = false;
                         FStar_TypeChecker_Env.check_uvars =
                           (uu___3655_27865.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq =
                           (uu___3655_27865.FStar_TypeChecker_Env.use_eq);
                         FStar_TypeChecker_Env.is_iface =
                           (uu___3655_27865.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (uu___3655_27865.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax = true;
                         FStar_TypeChecker_Env.lax_universes =
                           (uu___3655_27865.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (uu___3655_27865.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (uu___3655_27865.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (uu___3655_27865.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (uu___3655_27865.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.tc_term =
                           (uu___3655_27865.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.type_of =
                           (uu___3655_27865.FStar_TypeChecker_Env.type_of);
                         FStar_TypeChecker_Env.universe_of =
                           (uu___3655_27865.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.check_type_of =
                           (uu___3655_27865.FStar_TypeChecker_Env.check_type_of);
                         FStar_TypeChecker_Env.use_bv_sorts = true;
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (uu___3655_27865.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (uu___3655_27865.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (uu___3655_27865.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (uu___3655_27865.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (uu___3655_27865.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (uu___3655_27865.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (uu___3655_27865.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.postprocess =
                           (uu___3655_27865.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.is_native_tactic =
                           (uu___3655_27865.FStar_TypeChecker_Env.is_native_tactic);
                         FStar_TypeChecker_Env.identifier_info =
                           (uu___3655_27865.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (uu___3655_27865.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (uu___3655_27865.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (uu___3655_27865.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (uu___3655_27865.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (uu___3655_27865.FStar_TypeChecker_Env.erasable_types_tab)
                       }  in
                     ((let uu____27870 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env2)
                           (FStar_Options.Other "UniverseOf")
                          in
                       if uu____27870
                       then
                         let uu____27875 =
                           let uu____27877 =
                             FStar_TypeChecker_Env.get_range env2  in
                           FStar_Range.string_of_range uu____27877  in
                         let uu____27878 =
                           FStar_Syntax_Print.term_to_string hd3  in
                         FStar_Util.print2 "%s: About to type-check %s\n"
                           uu____27875 uu____27878
                       else ());
                      (let uu____27883 = tc_term env2 hd3  in
                       match uu____27883 with
                       | (uu____27904,{
                                        FStar_TypeChecker_Common.eff_name =
                                          uu____27905;
                                        FStar_TypeChecker_Common.res_typ = t;
                                        FStar_TypeChecker_Common.cflags =
                                          uu____27907;
                                        FStar_TypeChecker_Common.comp_thunk =
                                          uu____27908;_},g)
                           ->
                           ((let uu____27926 =
                               FStar_TypeChecker_Rel.solve_deferred_constraints
                                 env2 g
                                in
                             FStar_All.pipe_right uu____27926 (fun a1  -> ()));
                            (t, args1)))))
             in
          let uu____27937 = type_of_head true hd1 args  in
          (match uu____27937 with
           | (t,args1) ->
               let t1 =
                 FStar_TypeChecker_Normalize.normalize
                   [FStar_TypeChecker_Env.UnfoldUntil
                      FStar_Syntax_Syntax.delta_constant] env t
                  in
               let uu____27976 = FStar_Syntax_Util.arrow_formals_comp t1  in
               (match uu____27976 with
                | (bs,res) ->
                    let res1 = FStar_Syntax_Util.comp_result res  in
                    if (FStar_List.length bs) = (FStar_List.length args1)
                    then
                      let subst1 = FStar_Syntax_Util.subst_of_list bs args1
                         in
                      FStar_Syntax_Subst.subst subst1 res1
                    else
                      (let uu____28028 =
                         FStar_Syntax_Print.term_to_string res1  in
                       level_of_type_fail env e uu____28028)))
      | FStar_Syntax_Syntax.Tm_match (uu____28030,hd1::uu____28032) ->
          let uu____28097 = FStar_Syntax_Subst.open_branch hd1  in
          (match uu____28097 with
           | (uu____28098,uu____28099,hd2) -> universe_of_aux env hd2)
      | FStar_Syntax_Syntax.Tm_match (uu____28117,[]) ->
          level_of_type_fail env e "empty match cases"
  
let (universe_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.universe)
  =
  fun env  ->
    fun e  ->
      let uu____28164 = universe_of_aux env e  in
      level_of_type env e uu____28164
  
let (tc_tparams :
  FStar_TypeChecker_Env.env_t ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.binders * FStar_TypeChecker_Env.env *
        FStar_Syntax_Syntax.universes))
  =
  fun env  ->
    fun tps  ->
      let uu____28188 = tc_binders env tps  in
      match uu____28188 with
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
      | FStar_Syntax_Syntax.Tm_delayed uu____28246 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_bvar uu____28272 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x ->
          FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu____28278 = FStar_Syntax_Util.unfold_lazy i  in
          type_of_well_typed_term env uu____28278
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____28280 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env []
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____28280
            (fun uu____28294  ->
               match uu____28294 with
               | (t2,uu____28302) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_uinst
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____28304;
             FStar_Syntax_Syntax.vars = uu____28305;_},us)
          ->
          let uu____28311 =
            FStar_TypeChecker_Env.try_lookup_and_inst_lid env us
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_Util.bind_opt uu____28311
            (fun uu____28325  ->
               match uu____28325 with
               | (t2,uu____28333) -> FStar_Pervasives_Native.Some t2)
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify ) ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect
          uu____28334) -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_constant sc ->
          let uu____28336 = tc_constant env t1.FStar_Syntax_Syntax.pos sc  in
          FStar_Pervasives_Native.Some uu____28336
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu____28338 = mk_tm_type (FStar_Syntax_Syntax.U_succ u)  in
          FStar_Pervasives_Native.Some uu____28338
      | FStar_Syntax_Syntax.Tm_abs
          (bs,body,FStar_Pervasives_Native.Some
           { FStar_Syntax_Syntax.residual_effect = eff;
             FStar_Syntax_Syntax.residual_typ = FStar_Pervasives_Native.Some
               tbody;
             FStar_Syntax_Syntax.residual_flags = uu____28343;_})
          ->
          let mk_comp =
            let uu____28387 =
              FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid
               in
            if uu____28387
            then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_Total'
            else
              (let uu____28418 =
                 FStar_Ident.lid_equals eff
                   FStar_Parser_Const.effect_GTot_lid
                  in
               if uu____28418
               then
                 FStar_Pervasives_Native.Some FStar_Syntax_Syntax.mk_GTotal'
               else FStar_Pervasives_Native.None)
             in
          FStar_Util.bind_opt mk_comp
            (fun f  ->
               let uu____28488 = universe_of_well_typed_term env tbody  in
               FStar_Util.bind_opt uu____28488
                 (fun u  ->
                    let uu____28496 =
                      let uu____28499 =
                        let uu____28506 =
                          let uu____28507 =
                            let uu____28522 =
                              f tbody (FStar_Pervasives_Native.Some u)  in
                            (bs, uu____28522)  in
                          FStar_Syntax_Syntax.Tm_arrow uu____28507  in
                        FStar_Syntax_Syntax.mk uu____28506  in
                      uu____28499 FStar_Pervasives_Native.None
                        t1.FStar_Syntax_Syntax.pos
                       in
                    FStar_Pervasives_Native.Some uu____28496))
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____28559 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____28559 with
           | (bs1,c1) ->
               let rec aux env1 us bs2 =
                 match bs2 with
                 | [] ->
                     let uu____28618 =
                       universe_of_well_typed_term env1
                         (FStar_Syntax_Util.comp_result c1)
                        in
                     FStar_Util.bind_opt uu____28618
                       (fun uc  ->
                          let uu____28626 =
                            mk_tm_type (FStar_Syntax_Syntax.U_max (uc :: us))
                             in
                          FStar_Pervasives_Native.Some uu____28626)
                 | (x,imp)::bs3 ->
                     let uu____28652 =
                       universe_of_well_typed_term env1
                         x.FStar_Syntax_Syntax.sort
                        in
                     FStar_Util.bind_opt uu____28652
                       (fun u_x  ->
                          let env2 = FStar_TypeChecker_Env.push_bv env1 x  in
                          aux env2 (u_x :: us) bs3)
                  in
               aux env [] bs1)
      | FStar_Syntax_Syntax.Tm_abs uu____28661 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_refine (x,uu____28681) ->
          let uu____28686 =
            universe_of_well_typed_term env x.FStar_Syntax_Syntax.sort  in
          FStar_Util.bind_opt uu____28686
            (fun u_x  ->
               let uu____28694 = mk_tm_type u_x  in
               FStar_Pervasives_Native.Some uu____28694)
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_range_of );
             FStar_Syntax_Syntax.pos = uu____28699;
             FStar_Syntax_Syntax.vars = uu____28700;_},a::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____28779 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____28779 with
           | (unary_op1,uu____28799) ->
               let head1 =
                 let uu____28827 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a]))
                   FStar_Pervasives_Native.None uu____28827
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
             FStar_Syntax_Syntax.pos = uu____28875;
             FStar_Syntax_Syntax.vars = uu____28876;_},a1::a2::hd1::rest)
          ->
          let rest1 = hd1 :: rest  in
          let uu____28972 = FStar_Syntax_Util.head_and_args t1  in
          (match uu____28972 with
           | (unary_op1,uu____28992) ->
               let head1 =
                 let uu____29020 =
                   FStar_Range.union_ranges unary_op1.FStar_Syntax_Syntax.pos
                     (FStar_Pervasives_Native.fst a1).FStar_Syntax_Syntax.pos
                    in
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_app (unary_op1, [a1; a2]))
                   FStar_Pervasives_Native.None uu____29020
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
             FStar_Syntax_Syntax.pos = uu____29076;
             FStar_Syntax_Syntax.vars = uu____29077;_},uu____29078::[])
          -> FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_range
      | FStar_Syntax_Syntax.Tm_app
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
               (FStar_Const.Const_set_range_of );
             FStar_Syntax_Syntax.pos = uu____29117;
             FStar_Syntax_Syntax.vars = uu____29118;_},(t2,uu____29120)::uu____29121::[])
          -> type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
          let t_hd = type_of_well_typed_term env hd1  in
          let rec aux t_hd1 =
            let uu____29217 =
              let uu____29218 =
                FStar_TypeChecker_Normalize.unfold_whnf env t_hd1  in
              uu____29218.FStar_Syntax_Syntax.n  in
            match uu____29217 with
            | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                let n_args = FStar_List.length args  in
                let n_bs = FStar_List.length bs  in
                let bs_t_opt =
                  if n_args < n_bs
                  then
                    let uu____29291 = FStar_Util.first_N n_args bs  in
                    match uu____29291 with
                    | (bs1,rest) ->
                        let t2 =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_arrow (rest, c))
                            FStar_Pervasives_Native.None
                            t_hd1.FStar_Syntax_Syntax.pos
                           in
                        let uu____29379 =
                          let uu____29384 = FStar_Syntax_Syntax.mk_Total t2
                             in
                          FStar_Syntax_Subst.open_comp bs1 uu____29384  in
                        (match uu____29379 with
                         | (bs2,c1) ->
                             FStar_Pervasives_Native.Some
                               (bs2, (FStar_Syntax_Util.comp_result c1)))
                  else
                    if n_args = n_bs
                    then
                      (let uu____29438 = FStar_Syntax_Subst.open_comp bs c
                          in
                       match uu____29438 with
                       | (bs1,c1) ->
                           let uu____29459 =
                             FStar_Syntax_Util.is_tot_or_gtot_comp c1  in
                           if uu____29459
                           then
                             FStar_Pervasives_Native.Some
                               (bs1, (FStar_Syntax_Util.comp_result c1))
                           else FStar_Pervasives_Native.None)
                    else FStar_Pervasives_Native.None
                   in
                FStar_Util.bind_opt bs_t_opt
                  (fun uu____29541  ->
                     match uu____29541 with
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
                         let uu____29617 = FStar_Syntax_Subst.subst subst1 t2
                            in
                         FStar_Pervasives_Native.Some uu____29617)
            | FStar_Syntax_Syntax.Tm_refine (x,uu____29619) ->
                aux x.FStar_Syntax_Syntax.sort
            | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____29625,uu____29626) ->
                aux t2
            | uu____29667 -> FStar_Pervasives_Native.None  in
          FStar_Util.bind_opt t_hd aux
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29668,(FStar_Util.Inl t2,uu____29670),uu____29671) ->
          FStar_Pervasives_Native.Some t2
      | FStar_Syntax_Syntax.Tm_ascribed
          (uu____29718,(FStar_Util.Inr c,uu____29720),uu____29721) ->
          FStar_Pervasives_Native.Some (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_uvar (u,s) ->
          let uu____29786 =
            FStar_Syntax_Subst.subst' s u.FStar_Syntax_Syntax.ctx_uvar_typ
             in
          FStar_Pervasives_Native.Some uu____29786
      | FStar_Syntax_Syntax.Tm_quoted (tm,qi) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.t_term
      | FStar_Syntax_Syntax.Tm_meta (t2,uu____29794) ->
          type_of_well_typed_term env t2
      | FStar_Syntax_Syntax.Tm_match uu____29799 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_let uu____29822 ->
          FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Pervasives_Native.None
      | FStar_Syntax_Syntax.Tm_uinst uu____29836 ->
          FStar_Pervasives_Native.None

and (universe_of_well_typed_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____29847 = type_of_well_typed_term env t  in
      match uu____29847 with
      | FStar_Pervasives_Native.Some
          { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_type u;
            FStar_Syntax_Syntax.pos = uu____29853;
            FStar_Syntax_Syntax.vars = uu____29854;_}
          -> FStar_Pervasives_Native.Some u
      | uu____29857 -> FStar_Pervasives_Native.None

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
            let uu___3934_29885 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3934_29885.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3934_29885.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3934_29885.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3934_29885.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3934_29885.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3934_29885.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3934_29885.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3934_29885.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3934_29885.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3934_29885.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3934_29885.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3934_29885.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3934_29885.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3934_29885.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3934_29885.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3934_29885.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3934_29885.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3934_29885.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3934_29885.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3934_29885.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3934_29885.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3934_29885.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3934_29885.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3934_29885.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3934_29885.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3934_29885.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3934_29885.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3934_29885.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3934_29885.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3934_29885.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3934_29885.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3934_29885.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3934_29885.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3934_29885.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3934_29885.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3934_29885.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3934_29885.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3934_29885.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3934_29885.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3934_29885.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3934_29885.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3934_29885.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3934_29885.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3934_29885.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3934_29885.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____29892 =
            if must_total
            then
              let uu____29894 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____29894 with | (uu____29901,uu____29902,g) -> g
            else
              (let uu____29906 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____29906 with | (uu____29913,uu____29914,g) -> g)
             in
          let uu____29916 = type_of_well_typed_term env2 t  in
          match uu____29916 with
          | FStar_Pervasives_Native.None  -> slow_check ()
          | FStar_Pervasives_Native.Some k' ->
              ((let uu____29921 =
                  FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                    (FStar_Options.Other "FastImplicits")
                   in
                if uu____29921
                then
                  let uu____29926 =
                    FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos  in
                  let uu____29928 = FStar_Syntax_Print.term_to_string t  in
                  let uu____29930 = FStar_Syntax_Print.term_to_string k'  in
                  let uu____29932 = FStar_Syntax_Print.term_to_string k  in
                  FStar_Util.print4 "(%s) Fast check  %s : %s <:? %s\n"
                    uu____29926 uu____29928 uu____29930 uu____29932
                else ());
               (let g = FStar_TypeChecker_Rel.subtype_nosmt env2 k' k  in
                (let uu____29941 =
                   FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2)
                     (FStar_Options.Other "FastImplicits")
                    in
                 if uu____29941
                 then
                   let uu____29946 =
                     FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos
                      in
                   let uu____29948 = FStar_Syntax_Print.term_to_string t  in
                   let uu____29950 = FStar_Syntax_Print.term_to_string k'  in
                   let uu____29952 = FStar_Syntax_Print.term_to_string k  in
                   FStar_Util.print5 "(%s) Fast check %s: %s : %s <: %s\n"
                     uu____29946
                     (if FStar_Option.isSome g
                      then "succeeded with guard"
                      else "failed") uu____29948 uu____29950 uu____29952
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
            let uu___3965_29989 = env1  in
            {
              FStar_TypeChecker_Env.solver =
                (uu___3965_29989.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___3965_29989.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___3965_29989.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___3965_29989.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___3965_29989.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___3965_29989.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___3965_29989.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___3965_29989.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___3965_29989.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___3965_29989.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.is_pattern =
                (uu___3965_29989.FStar_TypeChecker_Env.is_pattern);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___3965_29989.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___3965_29989.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___3965_29989.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___3965_29989.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___3965_29989.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___3965_29989.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq =
                (uu___3965_29989.FStar_TypeChecker_Env.use_eq);
              FStar_TypeChecker_Env.is_iface =
                (uu___3965_29989.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___3965_29989.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax =
                (uu___3965_29989.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___3965_29989.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___3965_29989.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___3965_29989.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___3965_29989.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___3965_29989.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___3965_29989.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.type_of =
                (uu___3965_29989.FStar_TypeChecker_Env.type_of);
              FStar_TypeChecker_Env.universe_of =
                (uu___3965_29989.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.check_type_of =
                (uu___3965_29989.FStar_TypeChecker_Env.check_type_of);
              FStar_TypeChecker_Env.use_bv_sorts = true;
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___3965_29989.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___3965_29989.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___3965_29989.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___3965_29989.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___3965_29989.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___3965_29989.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___3965_29989.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.postprocess =
                (uu___3965_29989.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.is_native_tactic =
                (uu___3965_29989.FStar_TypeChecker_Env.is_native_tactic);
              FStar_TypeChecker_Env.identifier_info =
                (uu___3965_29989.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___3965_29989.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv =
                (uu___3965_29989.FStar_TypeChecker_Env.dsenv);
              FStar_TypeChecker_Env.nbe =
                (uu___3965_29989.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___3965_29989.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___3965_29989.FStar_TypeChecker_Env.erasable_types_tab)
            }  in
          let slow_check uu____29996 =
            if must_total
            then
              let uu____29998 = env2.FStar_TypeChecker_Env.type_of env2 t  in
              match uu____29998 with | (uu____30005,uu____30006,g) -> g
            else
              (let uu____30010 = env2.FStar_TypeChecker_Env.tc_term env2 t
                  in
               match uu____30010 with | (uu____30017,uu____30018,g) -> g)
             in
          let uu____30020 =
            let uu____30022 = FStar_Options.__temp_fast_implicits ()  in
            FStar_All.pipe_left Prims.op_Negation uu____30022  in
          if uu____30020
          then slow_check ()
          else check_type_of_well_typed_term' must_total env2 t k
  